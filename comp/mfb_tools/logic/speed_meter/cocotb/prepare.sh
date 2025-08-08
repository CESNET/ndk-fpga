#!/bin/sh
# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>

NDK_FPGA_PATH=../../../../..
source $NDK_FPGA_PATH/env.sh

ndk_fpga_venv_prepare "venv-mfb_speed_meter_mi"

pip install .

echo ""
echo "Now activate environment with:"
echo "source venv-mfb_speed_meter_mi/bin/activate"
