#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# pcap2sim.py: Convert PCAP file to FL_SIM(FL_BFM) file
# Copyright (C) 2010 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#

import sys
import struct

if len(sys.argv) != 3:
    print("Convert PCAP file to FL_SIM(FL_BFM) file.")
    print("Usage:")
    print("pcap2sim.py file.pcap file.sim")
    print("NOTE: FL_SIM file is generated with 1 part.")
    exit()

#pcap = pcapy.open_offline(sys.argv[1])
fpcap = open(sys.argv[1], "rb")
fsim = open(sys.argv[2], "wb")
code = fpcap.read(4)

if code == "\xa1\xb2\xc3\xd4":
    endianity = ">"
elif code == "\xd4\xc3\xb2\xa1":
    endianity = "<"

stopFlag = 0

pcapHeader = fpcap.read(20)

packetHeader = fpcap.read(16)
if len(packetHeader) < 16:
    stopFlag = 1
else:
    seconds, useconds, captureLength, wireLength = struct.unpack(endianity + "IIII", packetHeader)
    packet = fpcap.read(captureLength)

#pkt = pcap.next()
g = str()
while (stopFlag == 0):
    s = str()
    for i in range(0, len(packet)):
        b = hex(ord(packet[i]))
        if len(b) == 3:
            s = s + "0" + b[2]
        else:
            s = s + b[2] + b[3]
        #print(b)

    t = str()
    i = 0
    while i < len(s):
        n = str()
        if len(s) - i < 8:
            p = i
            if len(s) - p == 2:
                n = s[i] + s[i + 1]
                i = i + 2
            if len(s) - p == 4:
                n = s[i + 2] + s[i + 3] + s[i] + s[i + 1]
                i = i + 4
            if len(s) - p == 6:
                n = s[i + 4] + s[i + 5] + s[i + 2] + s[i + 3] + s[i] + s[i + 1]
                i = i + 6
        else:
            n = s[i + 6] + s[i + 7] + s[i + 4] + s[i + 5] + s[i + 2] + s[i + 3] + s[i] + s[i + 1]
            i = i + 8
        t = t + n + "\n"
    t = t + "#"
    #print(t)
    g = g + t + "\n"

    packetHeader = fpcap.read(16)
    if len(packetHeader) < 16:
        stopFlag = 1
    else:
        seconds, useconds, captureLength, wireLength = struct.unpack(endianity + "IIII", packetHeader)
        packet = fpcap.read(captureLength)

fpcap.close()
fsim.write(g)
fsim.close()
