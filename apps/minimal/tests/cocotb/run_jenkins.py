#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import json
import re
import subprocess
from pathlib import Path

JENKINSFILE = Path(__file__).parent / "top-level-sim.jenkinsfile"


def combinations():
    content = JENKINSFILE.read_text()

    match = re.search(r"COMBINATIONS_JSON = '''(.*?)'''", content, re.DOTALL)
    assert match, "could not find COMBINATIONS_JSON in top-level-sim.jenkinsfile"

    return json.loads(match.group(1))


def main():
    failed = []

    for combo in combinations():
        args = ["make"] + [f"{k}={v}" for k, v in combo.items()] + ["SIM_FLAGS=-c -do quit", "BMC_ENABLE=0"]

        if subprocess.run(args).returncode != 0:
            failed.append(" ".join(args[1:]))

    if failed:
        print("Failed combinations:")
        for f in failed:
            print(f"  {f}")


if __name__ == "__main__":
    main()
