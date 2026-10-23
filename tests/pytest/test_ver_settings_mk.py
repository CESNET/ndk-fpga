# test_ver_settings_mk.py: checks of the plain make run of a cocotb bench with the default setting of its ver_settings.py
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import importlib
import subprocess

import pytest

from flow_utils import MULTI_VER, REPO, make

SETTINGS = r'''
SETTINGS = {
    "default": {
        "DATA_WIDTH": "64",
        "DEVICE": "\\\"ULTRASCALE\\\"",
        "__cocotb_params__": {"TEST_FILTER": r"\.(first|second)\b"},
    },
    "narrow": {"DATA_WIDTH": "8"},
}
'''

# The environment of a recipe of the bench, as the cocotb run gets it.
PRINT_ENV = '--eval=print: ; @printf "%s\\n%s\\n" "$$GENERICS" "$$COCOTB_TEST_FILTER"'


@pytest.fixture
def mvd(monkeypatch):
    monkeypatch.syspath_prepend(str(MULTI_VER))
    return importlib.import_module("ver_settings_default")


@pytest.fixture
def bench(tmp_path):
    (tmp_path / "Makefile").write_text(
        "TOP_LEVEL_ENT=mi_pipe\n"
        f"TOP_LEVEL_PATH={REPO}/comp/mi_tools/pipe\n"
        f"include {MULTI_VER}/ver_settings.mk\n"
        f"include {REPO}/build/Makefile\n"
    )
    (tmp_path / "ver_settings.py").write_text(SETTINGS)
    return tmp_path


def run_env(bench, *args):
    result = make(bench, "--no-print-directory", PRINT_ENV, "print", *args)
    assert result.returncode == 0, result.stderr
    return result.stdout.split("\n")[:2]


def test_plain_run_gets_the_default_setting(bench):
    assert run_env(bench) == ['-gDATA_WIDTH=64 -gDEVICE="ULTRASCALE"', r"\.(first|second)\b"]


def test_given_generics_win(bench):
    """multi_ver_cocotb.py gives GENERICS and the COCOTB_* of its combination itself."""
    assert run_env(bench, "GENERICS=-gDATA_WIDTH=8 ") == ["-gDATA_WIDTH=8 ", ""]


def test_without_settings(bench):
    (bench / "ver_settings.py").unlink()
    assert run_env(bench) == ["", ""]


def test_unpassable_parameter_fails_make(bench):
    (bench / "ver_settings.py").write_text('SETTINGS = {"default": {"__cocotb_params__": {"TEST_FILTER": "a$"}}}\n')
    result = make(bench, "--no-print-directory", PRINT_ENV, "print")
    assert result.returncode != 0
    assert "cannot pass" in result.stderr


@pytest.mark.parametrize("value", ["8", "\\\"ULTRASCALE\\\"", "{30,20}", "\\[\\]"])
def test_shell_value(mvd, value):
    """The value the shell makes of a setting value inside the double quotes of multi_ver_cocotb.py's command."""
    shell = subprocess.run(["bash", "-c", f'printf %s "{value}"'], capture_output=True, text=True, check=True).stdout
    assert mvd.shell_value(value) == shell
