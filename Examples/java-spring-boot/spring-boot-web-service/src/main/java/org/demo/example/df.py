#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2020-2021 Intel Corp.
#                         Anjo Vahldiek-Oberwagner <anjo.lucas.vahldiek-oberwagner@intel.com>
#                         Dmitrii Kuvaiskii <dmitrii.kuvaiskii@intel.com>

import argparse
import hashlib
import os
import pathlib
import re
import shutil
import struct
import sys
import tempfile
import uuid

import docker  # pylint: disable=import-error
import jinja2
import shlex
import tomli   # pylint: disable=import-error
import tomli_w # pylint: disable=import-error
import yaml    # pylint: disable=import-error

class DistroRetrievalError(Exception):
    def __init__(self, *args):
        super().__init__(('Could not automatically detect the OS distro of the supplied Docker '
                         'image. Please specify OS distro manually in the configuration file.'),
                         *args)

def test_trueish(value):
    if not value:
        return False
    value = value.casefold()
    if value in ('false', 'off', 'no'):
        return False
    if value in ('true', 'on', 'yes'):
        return True
    if value.isdigit():
        return bool(int(value))
    raise ValueError(f'Invalid value for trueish: {value!r}')

def gsc_image_name(original_image_name):
    return f'gsc-{original_image_name}'

def gsc_unsigned_image_name(original_image_name):
    return f'gsc-{original_image_name}-unsigned'

def gsc_tmp_build_path(original_image_name):
    return pathlib.Path('build') / f'gsc-{original_image_name}'


def get_docker_image(docker_socket, image_name):
    try:
        docker_image = docker_socket.images.get(image_name)
        return docker_image
    except (docker.errors.ImageNotFound, docker.errors.APIError):
        return None


def build_docker_image(docker_api, build_path, image_name, dockerfile, **kwargs):
    build_path = str(build_path) # Docker API doesn't understand PathLib's PosixPath type
    stream = docker_api.build(path=build_path, tag=image_name, dockerfile=dockerfile,
                              decode=True, **kwargs)
    for chunk in stream:
        if 'stream' in chunk:
            for line in chunk['stream'].splitlines():
                print(line)


def extract_binary_info_from_image_config(config, env):
    entrypoint = config['Entrypoint'] or []
    num_starting_entrypoint_items = len(entrypoint)
    cmd = config['Cmd'] or []
    working_dir = config['WorkingDir'] or ''

    # Canonize working dir
    if working_dir == '':
        working_dir = '/'
    elif working_dir[-1] != '/':
        working_dir = working_dir + '/'

    # Some Docker images only use the optional CMD and have an empty entrypoint;
    # GSC has to make it explicit to prepare scripts and Intel SGX signatures
    entrypoint.extend(cmd)
    if not entrypoint:
        print('Could not find the entrypoint binary to the application image.')
        sys.exit(1)

    # Set binary to first executable in entrypoint and expand to full absolute path (if binary is
    # represented as relative path, e.g. `./my_app` or `some_dir/my_app`)
    binary = entrypoint[0]
    if not binary.startswith('/') and '/' in binary:
        binary = working_dir + binary

    # Check if we have fixed binary arguments as part of entrypoint
    if num_starting_entrypoint_items > 1:
        last_bin_arg = num_starting_entrypoint_items
        binary_arguments = entrypoint[1:last_bin_arg]
    else:
        last_bin_arg = 0
        binary_arguments = ''

    # Place the remaining optional arguments previously specified as command in the new command.
    # Necessary since the first element of the command may be the binary of the resulting image.
    cmd = entrypoint[last_bin_arg + 1:] if len(entrypoint) > last_bin_arg + 1 else ''

    env.globals.update({
        'binary': binary,
        'binary_arguments': binary_arguments,
        'binary_basename': os.path.basename(binary),
        'cmd': cmd,
        'working_dir': working_dir
    })


def extract_environment_from_image_config(config):
    env_list = config['Env'] or []
    base_image_environment = ''
    for env_var in env_list:
        # TODO: switch to loader.env_src_file = "file:file_with_serialized_envs" if
        # the need for multi-line envvars arises
        if '\n' in env_var:
            # we use TOML's basic single-line strings, can't have newlines
            print(f'Skipping environment variable `{env_var.split("=", maxsplit=1)[0]}`: '
                    'its value contains newlines.')
            continue
        escaped_env_var = env_var.translate(str.maketrans({'\\': r'\\', '"': r'\"'}))
        env_var_name = escaped_env_var.split('=', maxsplit=1)[0]
        env_var_value = escaped_env_var.split('=', maxsplit=1)[1]
        base_image_environment += f'loader.env.{env_var_name} = "{env_var_value}"\n'
    return base_image_environment

def extract_build_args(args):
    buildargs_dict = {}
    for item in args.build_arg:
        if '=' in item:
            key, value = item.split('=', maxsplit=1)
            buildargs_dict[key] = value
        else:
            # user specified --build-arg with key and without value, let's retrieve value from env
            if item in os.environ:
                buildargs_dict[item] = os.environ[item]
            else:
                print(f'Could not set build arg `{item}` from environment.')
                sys.exit(1)
    return buildargs_dict

def extract_define_args(args):
    defineargs_dict = {}
    for item in args.define:
        if '=' in item:
            key, value = item.split('=', maxsplit=1)
            defineargs_dict[key] = value
        else:
            print(f'Invalid value for argument `{item}`, expected `--define {item}=<value>`')
            sys.exit(1)
    return defineargs_dict

def extract_user_from_image_config(config, env):
    user = config['User']
    if not user:
        user = 'root'
    env.globals.update({'app_user': user})

def merge_manifests_in_order(manifest1, manifest2, manifest1_name, manifest2_name, path=[]):
    for key in manifest2:
        if key in manifest1:
            if isinstance(manifest1[key], dict) and isinstance(manifest2[key], dict):
                merge_manifests_in_order(manifest1[key], manifest2[key], manifest1_name,
                                         manifest2_name, path + [str(key)])
            elif isinstance(manifest1[key], list) and isinstance(manifest2[key], list):
                manifest1[key].extend(manifest2[key])
            elif manifest1[key] == manifest2[key]:
                pass
            else:
                # key exists in both manifests but with different values:
                # - for a special case of three below envvars must concatenate the values,
                # - in all other cases choose the value from the first manifest
                if ('.'.join(path) == 'loader.env' and
                        key in ['LD_LIBRARY_PATH', 'PATH', 'LD_PRELOAD']):
                    manifest1[key] = f'{manifest1[key]}:{manifest2[key]}'
                    print(f'Warning: Duplicate key `{".".join(path + [str(key)])}`. Concatenating'
                          f' values from `{manifest1_name}` and `{manifest2_name}`.')
                else:
                    print(f'Warning: Duplicate key `{".".join(path + [str(key)])}`. Overriding'
                          f' value from `{manifest2_name}` by the one in `{manifest1_name}`.')
        else:
            manifest1[key] = manifest2[key]
    return manifest1

def handle_redhat_repo_configs(distro, tmp_build_path):
    if not distro.startswith('redhat/'):
        return

    version_id_match = re.search(r'^redhat/ubi(\d+)(-minimal)?$', distro)
    if version_id_match:
        version_id = version_id_match.group(1)
        repo_name = f'rhel-{version_id}-for-x86_64-baseos-rpms'
    else:
        raise ValueError(f'Invalid Red Hat distro format: {distro}')

    with open('/etc/yum.repos.d/redhat.repo') as redhat_repo:
        redhat_repo_contents = redhat_repo.read()

        if not re.search(repo_name, redhat_repo_contents):
            print(f'Cannot find {repo_name} in /etc/yum.repos.d/redhat.repo. '
                  f'Register and subscribe your RHEL system to the Red Hat Customer '
                  f'Portal using Red Hat Subscription-Manager.')
            sys.exit(1)

        shutil.copyfile('/etc/yum.repos.d/redhat.repo', tmp_build_path / 'redhat.repo')
        pattern_sslclientkey = re.compile(r'(?<!#)sslclientkey\s*=\s*(.*)')
        pattern_sslcacert = re.compile(r'(?<!#)sslcacert\s*=\s*(.*)')

        match_sslclientkey = pattern_sslclientkey.search(redhat_repo_contents)
        if match_sslclientkey:
            sslclientkey_path = match_sslclientkey.group(1)
            sslclientkey_dir = os.path.dirname(sslclientkey_path)
        else:
            print(f'Cannot find SSL client key path in /etc/yum.repos.d/redhat.repo. '
                  f'Register and subscribe your RHEL system to the Red Hat Customer '
                  f'Portal using Red Hat Subscription-Manager.')
            sys.exit(1)

        match_sslcacert = pattern_sslcacert.search(redhat_repo_contents)
        if match_sslcacert:
            sslcacert_path = match_sslcacert.group(1)
        else:
            print(f'Cannot find SSL CA certificate path in /etc/yum.repos.d/redhat.repo. '
                  f'Register and subscribe your RHEL system to the Red Hat Customer '
                  f'Portal using Red Hat Subscription-Manager.')
            sys.exit(1)

        # The `redhat-uep.pem` file is used to validate the authenticity of Red Hat Update Engine
        # Proxy (UEP) server during updates and subscription management on the system.
        shutil.copyfile(sslcacert_path, tmp_build_path / 'redhat-uep.pem')

        if os.path.exists(tmp_build_path / 'pki'):
            shutil.rmtree(tmp_build_path / 'pki')

        # This directory stores the entitlement certificates for Red Hat subscriptions.
        # These files are used to authenticate and verify that a system is entitled to receive
        # software updates and support from Red Hat.
        shutil.copytree(sslclientkey_dir, tmp_build_path / 'pki/entitlement')

def handle_suse_repo_configs(distro, tmp_build_path):
    if not distro.startswith('registry.suse.com/suse/sle'):
        return

    if not os.path.exists('/etc/zypp/credentials.d/SCCcredentials'):
        print('Cannot find your SUSE Customer Center credentials file at '
                '/etc/zypp/credentials.d/SCCcredentials. Please register and subscribe your SUSE '
                'system to the SUSE Customer Center.')
        sys.exit(1)

    # This file contains the credentials for the SUSE Customer Center (SCC) account for the
    # system to authenticate and receive software updates and support from SUSE. Copy it to
    # the temporary build directory to include it in the graminized Docker image.
    shutil.copyfile('/etc/zypp/credentials.d/SCCcredentials', tmp_build_path / 'SCCcredentials')
