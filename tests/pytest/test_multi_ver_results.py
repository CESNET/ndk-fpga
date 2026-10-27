# test_multi_ver_results.py: checks that multi_ver_cocotb.py judges a run by the results.xml of that run
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import subprocess
import sys

import pytest

from flow_utils import MULTI_VER

PASSING_RESULTS = '<testsuites><testsuite name="all"><testcase name="cocotb_test.t"/></testsuite></testsuites>'


def multi_ver(bench, writes_results):
    """multi_ver_cocotb.py on a bench whose make run writes a passing results.xml or none, with a passing one left over."""
    recipe = f"\t@printf '%s' '{PASSING_RESULTS}' > results.xml\n" if writes_results else "\t@true\n"
    (bench / "Makefile").write_text("all:\n" + recipe)
    (bench / "ver_settings.py").write_text('SETTINGS = {"default": {"A": "1"}}\n')
    (bench / "results.xml").write_text(PASSING_RESULTS)
    return subprocess.run([sys.executable, str(MULTI_VER / "multi_ver_cocotb.py"), "ver_settings.py"], cwd=bench,
                          capture_output=True, text=True)


@pytest.mark.parametrize("writes_results, passes", [(True, True), (False, False)])
def test_run_without_results_fails(tmp_path, writes_results, passes):
    result = multi_ver(tmp_path, writes_results)
    assert (result.returncode == 0) == passes, result.stdout + result.stderr
    assert ("Run SUCCEEDED" in result.stdout) == passes
