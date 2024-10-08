#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import time
import random
import re
import signal
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

def nfb_dma_results(channel,rx=True):
    if rx==True:
        proc = subprocess.run("nfb-dma -i%d -r" % (channel),shell=True,check=True,stdout=subprocess.PIPE)
    else:
        proc = subprocess.run("nfb-dma -i%d -t" % (channel),shell=True,check=True,stdout=subprocess.PIPE)
    result = []
    stdout = proc.stdout.decode("utf-8")
    result_lines = stdout.split('\n')
    for line in result_lines:
        print(line)
        if rx==True:
            match = re.match(r"^.*(Received|Discarded).*:\s*([0-9]+)", line)
        else:
            match = re.match(r"^.*(Sent).*:\s*([0-9]+)", line)
        if match:
            result.append(int(match.group(2)))
    return result

def nfb_dma_reset():
    proc = subprocess.run("nfb-dma -R",shell=True,check=True,timeout=10)
    if proc.returncode > 0:
        print("Error: Unexpected error in nfb-dma.")
    return proc.returncode

def ndp_stop(proc):
    error = 0
    packet_count = 0
    bytes_count = 0
    proc.send_signal(signal.SIGINT)
    try:
        stdout, stderr = proc.communicate(timeout=10)
        proc.terminate()
    except TimeoutExpired:
        proc.kill()
        stdout, stderr = proc.communicate()
        print("Error: Unexpected error in ndp process.")
        error = 1
    stdout = stdout.decode("utf-8")
    result_lines = stdout.split('\n')
    for line in result_lines:
        print(line)
    for line in result_lines:
        match = re.match(r"^ERROR:.*", line)
        if match:
            print("Corrupted frame(s) found during the test")
            error = 1
        match = re.match(r"^(Packets).*:\s*([0-9]+)", line)
        if match:
            packet_count = int(match.group(2))
        match = re.match(r"^(Bytes).*:\s*([0-9]+)", line)
        if match:
            bytes_count = int(match.group(2))
    return (packet_count,bytes_count,error)

def dma_channel_check(channel,frame_size,rx):
    error = nfb_dma_reset()
    if error > 0:
        return error
    if rx:
        hw_cnt_offset = 0
        dir_s = "RX"
        ndp = subprocess.Popen("ndp-read -i%d" % (channel),shell=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        # RX generator - stop
        nfb_bus(0x5080,0,0)
        # RX set loopback mux
        nfb_bus(0x5000,0,0)
        # RX set generator mux
        nfb_bus(0x5008,0,1)
        # RX generator - set size
        nfb_bus(0x5084,0,frame_size)
        # RX generator - start
        nfb_bus(0x5080,0,1)
        time.sleep(4)
        # RX generator - stop
        nfb_bus(0x5080,0,0)
        time.sleep(0.2)
    else:
        hw_cnt_offset = 2
        dir_s = "TX"
        # RX set loopback mux
        nfb_bus(0x5000,0,1)
        # TX set generator mux
        nfb_bus(0x500C,0,1)
        # start ndp-generate
        ndp = subprocess.Popen("ndp-generate -i%d -s%d" % (channel,frame_size),shell=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        time.sleep(4)

    packet_count, bytes_count, ndp_error = ndp_stop(ndp)
    hw_cnt = nfb_dma_results(channel)
    print("Info: Packet counters: SW = %d, HW %d." %(packet_count, hw_cnt[0]))
    print("Info: Bytes counters: Sw = %d, HW %d." %(bytes_count, hw_cnt[1]))
    if hw_cnt[hw_cnt_offset] != packet_count:
        print("Error: Packet counters do not match.")
        error = 1
    if hw_cnt[hw_cnt_offset+1] != bytes_count:
        print("Error: Bytes counters do not match.")
        error = 1
    if error == 0:
        print("Info: The %s DMA test (channel: %d, frame size: %d) has PASSed." %(dir_s,channel,frame_size))
    if ndp_error > 0:
        print("Error: Unexpected error in NDK tools.")
        error = 1
    return error

def dma_loopback_basic(channels=32):
    print("Info: Starting DMA loopback test...")
    print("Info: all channels, random frame size in range 64 to 2048 bytes")
    dis_pkt = 0
    dis_bts = 0
    error = nfb_dma_reset()
    if error > 0:
        return error
    # RX set loopback mux
    nfb_bus(0x5000,0,1)
    # TX set generator mux
    nfb_bus(0x500C,0,1)
    ndp_rd = subprocess.Popen("ndp-read",shell=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    ndp_gn = subprocess.Popen("ndp-generate -s64-2048",shell=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    time.sleep(4)
    gen_pkt, gen_bts, ndp_gn_error = ndp_stop(ndp_gn)
    rd_pkt, rd_bts, ndp_rd_error = ndp_stop(ndp_rd)
    for i in range(channels):
        hw_cnt = nfb_dma_results(i)
        dis_pkt = dis_pkt + hw_cnt[2]
        dis_bts = dis_bts + hw_cnt[3]
    print("Info: Packet counters: generator = %d, reader %d, discard %d." %(gen_pkt, rd_pkt, dis_pkt))
    print("Info: Bytes counters: generator = %d, reader %d, discard %d." %(gen_bts, rd_bts, dis_bts))
    if rd_pkt != (gen_pkt-dis_pkt):
        print("Error: Packet counters do not match.")
        error = 1
    if rd_bts != (gen_bts-dis_bts):
        print("Error: Bytes counters do not match.")
        error = 1
    if (ndp_gn_error > 0) or (ndp_rd_error > 0):
        print("Error: Unexpected error in NDK tools.")
        error = 1
    return error

def dma_loopback(channels=32):
    print("Info: Starting DMA loopback data integrity test...")
    print("Info: all channels, random frame size in range 64 to 2048 bytes")
    error = nfb_dma_reset()
    if error > 0:
        return error
    # RX set loopback mux
    nfb_bus(0x5000,0,1)
    # TX set generator mux
    nfb_bus(0x500C,0,1)
    ndp = subprocess.Popen("ndp-loopback-hw -s64-2048",shell=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    time.sleep(5)
    gen_pkt, gen_bts, ndp_error = ndp_stop(ndp)
    hw_pkt = 0
    hw_bts = 0
    for i in range(channels):
        hw_cnt = nfb_dma_results(i,False)
        hw_pkt = hw_pkt + hw_cnt[0]
        hw_bts = hw_bts + hw_cnt[1]
    print("Info: Packet counters: generator = %d, discard %d." %(gen_pkt, hw_pkt))
    print("Info: Bytes counters: generator = %d, discard %d." %(gen_bts, hw_bts))
    if hw_pkt != gen_pkt:
        print("Error: Packet counters do not match.")
        error = 1
    if hw_bts != gen_bts:
        print("Error: Bytes counters do not match.")
        error = 1
    if ndp_error > 0:
        print("Error: Unexpected error in NDK tools.")
        error = 1
    return error

# TEST FUNCTIONS
# ==============================================================================

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

def check_pcie_device_in_lspci():
    print("Info: Print all devices in lspci:")
    subprocess.call("lspci",shell=True)
    print("Info: Try find our device in lspci...:")
    rt=subprocess.call("lspci | grep 'Ethernet controller: Cesnet, z.s.p.o.'",shell=True)
    if rt > 0:
        print("Error: The card is not visible in the PCI device list.")
    return rt

def test_check_pcie_device_in_lspci():
    assert check_pcie_device_in_lspci() == 0

def mi_bus_random_rw_access():
    error_cnt = 0
    dwr_list = []
    print("Info: Starting MI bus test...")
    for i in range(64):
        dwr_list.append(random.randint(0,(2**32-1)))
        nfb_bus((i*4),0,dwr_list[i])
        print("Info: MI write %d to %d" %(dwr_list[i],i*4))
    for i in range(64):
        drd = nfb_bus(i*4)
        print("Info: MI read %s from %s" %(hex(drd),hex(i*4)))
        if drd != (dwr_list[i]):
            error_cnt = error_cnt + 1
    if error_cnt > 0:
        print("Error: Some MI requests failed. Read error counts: %d" %(error_cnt)) 
    return error_cnt

@pytest.mark.depends(on=['test_check_pcie_device_in_lspci','test_check_ndk_sw'])
def test_mi_bus_random_rw_access():
    assert mi_bus_random_rw_access() == 0

@pytest.mark.depends(on=['test_check_pcie_device_in_lspci','test_check_ndk_sw'])
@pytest.mark.parametrize("channels", range(32))
@pytest.mark.parametrize("frame_size", [64,256,1024])
def test_dma_rx_channels(channels,frame_size):
    assert dma_channel_check(channels,frame_size,True) == 0
    
@pytest.mark.depends(on=['test_check_pcie_device_in_lspci','test_check_ndk_sw'])
@pytest.mark.parametrize("channels", range(32))
@pytest.mark.parametrize("frame_size", [64,256,1024])
def test_dma_tx_channels(channels,frame_size):
    assert dma_channel_check(channels,frame_size,False) == 0

@pytest.mark.depends(on=['test_check_pcie_device_in_lspci','test_check_ndk_sw'])
def test_dma_loopback_basic():
    assert dma_loopback_basic() == 0

@pytest.mark.depends(on=['test_check_pcie_device_in_lspci','test_check_ndk_sw'])
def test_dma_loopback_data_integrity():
    assert dma_loopback() == 0
