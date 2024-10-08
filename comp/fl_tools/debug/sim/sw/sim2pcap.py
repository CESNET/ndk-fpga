#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# sim2pcap.py: Convert FL_SIM(FL_BFM) file to PCAP file
# Copyright (C) 2010 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#

import sys
import re
import struct

if len(sys.argv) != 3:
    print("Convert FL_SIM(FL_BFM) file to PCAP file.")
    print("Usage:")
    print("sim2pcap.py file.sim file.pcap")
    print("NOTE: FL_SIM files with only 1 part are supported. Use cut_packet.py to extract packets from multipart FL_SIM file.")
    exit()

fsim = open(sys.argv[1], "rb")
fpcap = open(sys.argv[2], "wb")
blob = fsim.read()
fpcap.write(struct.pack("IHHIIII", 0xa1b2c3d4, 2, 4, 0, 0, 1600, 1))
parts = re.split("#\n", blob)
for i in range(0, len(parts)):
    if len(parts[i]) > 0:
        s = str()
        words = re.split("\n", parts[i])
        for j in range(0, len(words)):
            if len(words[j]) > 0:
                if len(words[j]) == 2:
                    s += words[j][0] + words[j][1]
                if len(words[j]) == 4:
                    s += words[j][2] + words[j][3] + words[j][0] + words[j][1]
                if len(words[j]) == 6:
                    s += words[j][4] + words[j][5] + words[j][2] + words[j][3] + words[j][0] + words[j][1]
                if len(words[j]) == 8:
                    s += words[j][6] + words[j][7] + words[j][4] + words[j][5] + words[j][2] + words[j][3] + words[j][0] + words[j][1]
        d = str()
        j = 0
        while j < len(s):
            b = s[j] + s[j + 1]
            j = j + 2
            d += chr(int(b, 16))
        length = len(d)
        seconds = 0
        useconds = 0
        captureLength = length
        wireLength = length
        fpcap.write(struct.pack("IIII", seconds, useconds, captureLength, wireLength))
        fpcap.write(d)
fsim.close()
fpcap.close()
