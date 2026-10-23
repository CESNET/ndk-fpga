# test_nvc_flow.py: make-level checks of the cocotb simulation targets in build/common.mk
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import re
import shlex
import shutil
import subprocess

import pytest

from flow_utils import REPO, make, write_makefile

pytestmark = pytest.mark.skipif(
    shutil.which("nvc") is None or shutil.which("cocotb-config") is None, reason="needs nvc and cocotb"
)

# The make target, the simulator it starts and the argument of the simulator's cocotb run.
COCOTB_RUNS = [("nvc-sim", "nvc", "-r"), ("ghdl-sim", "ghdl", "-r")]

ASSIGNMENT = re.compile(r"[A-Za-z_]\w*=")


@pytest.fixture
def bench(tmp_path):
    """A bench directory for MI_PIPE, which elaborates and runs without any stimulus."""
    write_makefile(tmp_path, "mi_pipe", REPO / "comp" / "mi_tools" / "pipe")
    return tmp_path


def dry_run(directory, *args):
    """Commands of a make run as (program, environment, arguments). The source list is generated for real, as only the
    inner make of the two-phase flow gets -n."""
    result = make(directory, "MAKE=make -n", *args)
    assert result.returncode == 0, result.stderr
    commands = []
    for line in result.stdout.replace("\\\n", " ").splitlines():
        try:
            tokens = shlex.split(line)
        except ValueError:
            continue
        env = {}
        while tokens and ASSIGNMENT.match(tokens[0]):
            name, _, value = tokens.pop(0).partition("=")
            env[name] = value
        if tokens:
            commands.append((tokens[0], env, tokens[1:]))
    return commands


def step(commands, program, flag):
    """Environment and arguments of the one command of program that has flag, e.g. the -r step of nvc."""
    found = [(env, args) for name, env, args in commands if name == program and flag in args]
    assert len(found) == 1, found
    return found[0]


@pytest.mark.parametrize("target, program, flag", COCOTB_RUNS)
def test_cocotb_environment(bench, target, program, flag):
    env, _ = step(dry_run(bench, f"TARGET={target}"), program, flag)
    assert env["MODULE"] == env["COCOTB_TEST_MODULES"] == "cocotb_test"
    assert env["TOPLEVEL"] == "mi_pipe"
    assert env["TOPLEVEL_LANG"] == "vhdl"
    assert env["COCOTB_RESOLVE_X"] == "ZEROS"
    assert env["PYGPI_PYTHON_BIN"] == subprocess.check_output(["cocotb-config", "--python-bin"], text=True).strip()
    assert env["GPI_USERS"]


@pytest.mark.parametrize("target, program, flag", COCOTB_RUNS)
def test_user_env_overrides_cocotb_defaults(bench, target, program, flag):
    user_env = "USER_ENV=PYGPI_PYTHON_BIN=/opt/python GPI_USERS=libcustom.so"
    env, _ = step(dry_run(bench, f"TARGET={target}", user_env), program, flag)
    assert env["PYGPI_PYTHON_BIN"] == "/opt/python"
    assert env["GPI_USERS"] == "libcustom.so"
