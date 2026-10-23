# flow_utils.py: helpers shared by the flow tests in this directory
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import os
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]


def make(directory, *args):
    """make in directory without the SIM of the caller's environment, which would turn a TARGET=cocotb run into nvc."""
    env = {name: value for name, value in os.environ.items() if name != "SIM"}
    return subprocess.run(["make", "-C", str(directory), *args], capture_output=True, text=True, env=env)


def write_makefile(directory, entity, path):
    (directory / "Makefile").write_text(
        f"TOP_LEVEL_ENT={entity}\n"
        f"TOP_LEVEL_PATH={path}\n"
        ".PHONY: all\n"
        "all: comp\n"
        f"include {REPO}/build/Makefile\n"
    )
