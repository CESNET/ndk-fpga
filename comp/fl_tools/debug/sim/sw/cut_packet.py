#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# cut_packet.py: Cut(extract) one part from FL_SIM(FL_BFM) file
# Copyright (C) 2010 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#

import sys
import re

if len(sys.argv) != 4:
    print("Cut 1 part from multipart FL_SIM(FL_BFM) file.")
    print("Usage:")
    print("cut_packet in.sim out.sim PART")
    print("PART - part with packet, start with 0")
    exit()

fin = open(sys.argv[1], "rb")
fout = open(sys.argv[2], "wb")

blob = fin.read()

parts = re.split("#\n", blob)

t = str()

for i in range(0, len(parts)):
    if len(parts[i]) > 0:
        in_parts = re.split("\\$\n", parts[i])

        for j in range(0, len(in_parts)):
            if (len(in_parts[j]) > 0):
                if j == int(sys.argv[3]):
                    t = t + in_parts[j] + "#\n"

fout.write(t)

fout.close()
fin.close()
