#!/bin/sh

NDK_FPGA_PATH=../../../../../../../..

source $NDK_FPGA_PATH/env.sh

ndk_fpga_venv_prepare "venv-rx_mac_seg"

pip install -e .
#pip install "cocotbext-ofm[nfb]@$NDK_FPGA_COCOTBEXT_OFM_URL"
