#!/bin/sh
# Example script for preparing ndk-app repository to run top-level cocotb simulation
# Run it once in the build/CARD folder !

# Check base folder
ls ../../ndk/core/intel/cocotb/examples/cocotb_test.py > /dev/null
if [ $! ]; then
	echo "Run this script in the build/CARD folder!"
	exit 1
fi

# These commands already done on preklad machines:
# pip3 install cocotb
# pip3 install cocotb-bus
# pip3 install fdt
# git clone https://github.com/dgibson/dtc.git --branch v1.6.0
# (cd dtc; make; cd pylibfdt; python3.9 setup.py install --user)

# Install cocotbext-ofm and its cocotbext.axi4stream dependency
pip3 install git+https://github.com/martinspinler/cocotbext-axi4stream.git#egg=cocotbext.axi4stream -U
pip3 install git+ssh://git@gitlab.liberouter.org/ndk/cocotbext.git#egg=cocotbext-ofm -U

# Use example test
cp ../../ndk/core/intel/cocotb/examples/cocotb_test* ./

# Run simulation:
# make TARGET=cocotb
echo "Now run simulation with command: make TARGET=cocotb"
