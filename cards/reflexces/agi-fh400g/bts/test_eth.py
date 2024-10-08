#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import time
import random
import re
import signal
import os
import subprocess
# pytest, pytest-depends, pytest-html
import pytest

# AUXILIARY FUNCTIONS
# ==============================================================================

def nfb_bus(addr,pcie_index=0,value=None):
    if (value==None): # read
        return int("0x"+subprocess.Popen("nfb-bus -i%d %s" % (pcie_index,hex(addr)),shell=True,stdout=subprocess.PIPE).stdout.read().strip().decode("utf-8"),16)
    else: # write
        return subprocess.call("nfb-bus -i%d %s %s" % (pcie_index,hex(addr),hex(value)),shell=True)

def nfb_eth_results(channel,rx=True):
    if rx==True:
        proc = subprocess.run("nfb-eth -i%d -r" % (channel),shell=True,check=True,stdout=subprocess.PIPE)
    else:
        proc = subprocess.run("nfb-eth -i%d -t" % (channel),shell=True,check=True,stdout=subprocess.PIPE)
    result = []
    stdout = proc.stdout.decode("utf-8")
    result_lines = stdout.split('\n')
    for line in result_lines:
        print(line)
        if rx==True:
            match = re.match(r"^.*(Processed|Received|Erroneous).*:\s*([0-9]+)", line)
        else:
            match = re.match(r"^.*(Processed|Transmitted|Erroneous).*:\s*([0-9]+)", line)
        if match:
            print(match)
            result.append(int(match.group(2)))
    return result

def nfb_eth_enable():
    os.system("nfb-eth -e1")
    return

def nfb_eth_reset():
    os.system("nfb-eth -R")
    return

def nfb_eth_set_mac_filter(gen_offset):
    # Enable MAC filter on RX
    os.system("nfb-eth -rM normal")
    # Clear MAC table on RX
    os.system("nfb-eth -rM clear")
    # Set allowed Destination MAC
    os.system("nfb-eth -rM add 11:22:33:44:55:66")
    # Set Destination MAC to FPGA generator
    nfb_bus(gen_offset+0x10,0,0x44332211)
    nfb_bus(gen_offset+0x14,0,0x6655)
    return

def generator_stop(gen_offset):
    # generator - stop
    nfb_bus(gen_offset,0,0)
    return

def generator_run(gen_offset,frame_size):
    # generator - set size
    nfb_bus(gen_offset+0x4,0,frame_size)
    # generator - start
    nfb_bus(gen_offset,0,1)
    return

def gls_setup(gls_offset,rx_loop,tx_loop,rx_gen,tx_gen):
    nfb_bus(gls_offset,0,rx_loop)
    nfb_bus(gls_offset+0x4,0,tx_loop)
    nfb_bus(gls_offset+0x8,0,rx_gen)
    nfb_bus(gls_offset+0xC,0,tx_gen)
    return

# TEST FUNCTIONS
# ==============================================================================

gls_offset = 0x5000
tx_gen_offset = 0x50C0

def check_ndk_sw():
    print("Info: Check NDK software tools:")
    rt=subprocess.call(['which', 'nfb-info'])
    if rt > 0:
        print("Error: NDK software is not installed.")
        return rt
    print("Info: Check NDK driver debug mode:")
    rt=subprocess.call("nfb-bus 0x0",shell=True)
    if rt > 0:
        print("Error: NDK driver is not debug mode.")
    return rt

def test_check_ndk_sw():
    assert check_ndk_sw() == 0

@pytest.mark.depends(on=['test_check_ndk_sw'])
@pytest.mark.parametrize("frame_size", range(64, 1518, 32)) 
def test_eth_loopback_mac_filter(frame_size):
    error = 0
    generator_stop(tx_gen_offset)
    gls_setup(gls_offset,0x0,0x0,0x1,0x1)
    nfb_eth_enable()
    nfb_eth_set_mac_filter(tx_gen_offset)
    nfb_eth_reset()
    generator_run(tx_gen_offset,frame_size-4)
    time.sleep(2)
    generator_stop(tx_gen_offset)
    time.sleep(0.5)
    rx_abts, rx_ppts, rx_apts, rx_errs = nfb_eth_results(0,True)
    tx_abts, tx_ppts, tx_apts, tx_errs = nfb_eth_results(0,False)
    print("Info: Processed Packet counters: TX = %d, RX %d." %(tx_ppts, rx_ppts))
    print("Info: Accepted Packet counters: TX = %d, RX %d." %(tx_apts, rx_apts))
    print("Info: Error Packet counters: TX = %d, RX %d." %(tx_errs, rx_errs))
    print("Info: Accepted Bytes counters: TX = %d, RX %d." %(tx_abts, rx_abts))
    if rx_ppts != rx_ppts:
        print("Error: Processed Packet counters do not match.")
        error = 1
    if rx_apts != tx_apts:
        print("Error: Accepted Packet counters do not match.")
        error = 1
    if rx_abts != tx_abts:
        print("Error: Accepted Bytes counters do not match.")
        error = 1
    if (rx_errs > 0) or (tx_errs > 0):
        print("Error: Unexpected error packets.")
        error = 1
    assert error == 0
