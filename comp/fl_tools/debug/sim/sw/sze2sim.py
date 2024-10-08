#!/bin/python
# -*- coding: iso-8859-2 -*-

import sys

if len(sys.argv) != 3:
    print("Convert SZE2LOOPBACK output to FL_BFM file.")
    print("Usage:")
    print("sze2sim.py file.sze file.sim")
    exit()

state = 'B'
ln = 1
f = open(sys.argv[1], 'r')
fsim = open(sys.argv[2], 'w')
text = f.read()
f.close()
lines = text.splitlines()
for line in lines:
    d = line.split()
    #begin of packet == "R" or "W"
    if state == 'B':
        if line[0] != 'R' and line[0] != 'W':
            sys.exit("Chyba na riadku %d - stav B" % ln)
        state = 'H1'
    #first piece of header == "hdr : 0000 | 0000 :  XX XX XX XX"
    elif state == 'H1':
        if not line.startswith('hdr'):
            sys.exit("Chyba na riadku %d - stav H1" % ln)
        length = int(d[6], 16) + int(d[7], 16) * 255
        res = d[6:]
        state = 'H2'
    #second piece of header == "hw  : 0004 | 0000 :  ..."
    elif state == 'H2':
        if not line.startswith('hw'):
            sys.exit("Chyba na riadku %d - stav H2" % ln)
        res += d[6:]
        state = 'D'
    #packet data
    elif state == 'D':
        if not line.startswith('sw'):
            sys.exit("Chyba na riadku %d - stav D" % ln)
        res += d[6:]
        if len(res) == length:
            state = 'B'
            fsim.write(res[3] + res[2] + res[1] + res[0] + "\n")
            fsim.write(res[7] + res[6] + res[5] + res[4] + "\n")
            fsim.write(res[11] + res[10] + res[9] + res[8] + "\n")
            fsim.write(res[15] + res[14] + res[13] + res[12] + "\n")
            fsim.write('$' + "\n")
            for i in range(16, length - 3, 4):
                fsim.write(res[i + 3] + res[i + 2] + res[i + 1] + res[i] + "\n")
            if length % 4 != 0:
                fsim.write("".join(res[((length / 4) * 4):]) + "\n")
            fsim.write('#' + "\n")
        else:
            state = 'D'
    ln += 1
fsim.close()
if state != 'B':
    sys.exit("Nacakany EOF")
