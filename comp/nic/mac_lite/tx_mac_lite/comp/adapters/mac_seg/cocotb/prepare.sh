#!/bin/sh

NDK_FPGA_PATH=../../../../../../../..

source $NDK_FPGA_PATH/env.sh

ndk_fpga_venv_prepare "venv-tx_mac_seg"

pip install .

