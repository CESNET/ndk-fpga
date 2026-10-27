# ver_settings_default.py: the "default" setting of a ver_settings.py for a plain make run of a cocotb bench
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0
"""``ver_settings_default.py --generics <file>`` prints GENERICS as the make run of multi_ver_cocotb.py gets it,
``--cocotb-env <file>`` a make assignment COCOTB_<K>?=<V> for each key K of "__cocotb_params__". ver_settings.mk
reads both."""

import argparse
import copy
import runpy
import shlex
import sys


def default_setting(settings_file):
    """The "default" setting of a ver_settings.py, as multi_ver_cocotb.py applies it to every combination."""
    return copy.deepcopy(runpy.run_path(settings_file)["SETTINGS"]["default"])


def shell_value(value):
    """A setting value as the shell leaves it inside the double quotes of multi_ver_cocotb.py's GENERICS="..."."""
    return shlex.split(f'"{value}"')[0]


def generics(setting):
    return " ".join(f"-g{name}={shell_value(value)}" for name, value in setting.items() if not name.startswith("__"))


def cocotb_env(setting):
    """The words are evaluated by make, so a value must not contain what make or a word split would change."""
    words = []
    for name, value in setting.get("__cocotb_params__", {}).items():
        if any(char in value for char in " \t\n#$"):
            sys.exit(f"__cocotb_params__ {name}={value!r}: whitespace, '#' and '$' cannot pass through make")
        words.append(f"COCOTB_{name}?={value}")
    return " ".join(words)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    what = parser.add_mutually_exclusive_group(required=True)
    what.add_argument("--generics", action="store_true")
    what.add_argument("--cocotb-env", action="store_true")
    parser.add_argument("settings_file")
    args = parser.parse_args()
    setting = default_setting(args.settings_file)
    print(generics(setting) if args.generics else cocotb_env(setting))
