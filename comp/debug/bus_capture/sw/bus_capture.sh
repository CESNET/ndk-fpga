#!/bin/bash
# bus_capture.sh:
# Copyright (C) 2019 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Getting parameters
addr_base=$1 #IBUF base addr + 0x100; 0x8000+0x100=0x8100
bus_width=$((64+8)) #$2
dwords=$((($bus_width+31)/32))
items=4096

# registers address
cmd_addr=$addr_base
dly_addr=$(printf '0x%x' $(($addr_base+0x4)))
sel_addr=$(printf '0x%x' $(($addr_base+0x8)))
cap_addr=$(printf '0x%x' $(($addr_base+0xC)))

echo "Status register ($cmd_addr):"
nfb-bus $cmd_addr

echo "Delay register ($dly_addr):"
nfb-bus $dly_addr

echo "Ready to read captured data."
# read setup
nfb-bus $cmd_addr 0x1
echo "Initial read address was set."

for ((item=0;item<$items;item++))
do
    # read enable
    nfb-bus $cmd_addr 0x2
    # read all 32bit dwords
    for ((dword=0;dword<$dwords;dword++))
    do
        # set select register
        nfb-bus $sel_addr $(printf '0x%x' $dword)
        # read capture register
        nfb-bus $cap_addr
    done
done

echo "The captured data has been read."

# capture reset
#nfb-bus $cmd_addr 0x3
