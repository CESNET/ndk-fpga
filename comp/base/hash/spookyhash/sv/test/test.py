# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>
#
# Pytest test executing simulation of testbench.sv for key lengths ranging from 1B to 191B.

import os
import pytest

KEY_WIDTH_VALUES = list(range(8, 1529, 8))
TEST_LOG_DIR = "test_logs"

if os.path.exists(TEST_LOG_DIR):
    os.system(f"rm -r {TEST_LOG_DIR}")
os.mkdir(TEST_LOG_DIR)


@pytest.mark.parametrize("key_width", KEY_WIDTH_VALUES)
def test_spooky(key_width: int) -> str:
    print(f"Running with KEY_WIDTH={key_width}:")

    os.system(f"make run KEY_WIDTH={key_width} > /dev/null 2>&1")

    assert os.path.exists("transcript"), "\tFAILED => transcript not found!\n"

    log_file = open("transcript", "r")
    log = log_file.read()
    log_file.close()

    if "Errors: 0" not in log:
        log_file = open(f"{TEST_LOG_DIR}/log_fail_{key_width}", "w+")
        log_file.write(log)
        log_file.close()

        raise RuntimeError("\tFAILED: Errors detected!\n")

    print("\tSUCCESS\n")
