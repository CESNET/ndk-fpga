#!/bin/python3

# max_words_num_transcript_check.py: Check protocol integrity
# Copyright (C) 2018 CESNET z. s. p. o.
# Author(s): Jan Kubalek

import math
from random import randint
import os.path
import sys

DOWN_REGIONS = 4
DOWN_REG_SIZE = 4
UP_ADDR_WIDTH = 64
UP_LEN_WIDTH = 11

DOWN_W_D = DOWN_REGIONS * DOWN_REG_SIZE
DOWN_W_L = int(math.log(DOWN_W_D, 2))
REG_SIZE_L = int(math.log(DOWN_REG_SIZE, 2))
REGS_L = int(math.log(DOWN_REGIONS, 2))

RCB = 0
RCBS = 64 // 4 if RCB == 0 else 128 // 4
RCBL = int(math.log(RCBS, 2))


# prints one MFB word as bitmap of data and empty spaces
def get_word_string(word_bitmap):
    # word bitmap ex: 0001 1111 0000 0000 -> region 2 full; region 3 contains 1 dword
    t = "|"
    for r in range(DOWN_REGIONS):
        for d in range(DOWN_REG_SIZE):
            t = ("#" if (word_bitmap & 1) == 1 else " ") + t
            word_bitmap >>= 1
        t = "|" + t
    return t


# prints multiple MFB words as bitmap
def print_word_bitmaps(bitmap_arr):
    rs0 = DOWN_REG_SIZE // 2
    rs1 = DOWN_REG_SIZE - rs0 - 1
    s = " "
    for i in range(DOWN_REGIONS - 1, -1, -1):
        s += " " * rs0 + str(i) + " " * rs1 + " "
    print("region: " + s)
    dl = "-" * (DOWN_REGIONS * (DOWN_REG_SIZE + 1) + 1)
    print("        " + dl)
    for i in range(len(bitmap_arr)):
        print("  word: " + get_word_string(bitmap_arr[i]) + " " + str(i))
        print("        " + dl)


# words count simulation (with print)
def words_count_long(a, s):
    a  = a >> 2 # convert to DWORD address
    al = a + s    # addr + length number = end addr

    u_start = False
    w_arr = []
    if RCB == 1:
        if (a & (RCBS - 1)) != 0: # unaligned start
            u_start = True

    # u_end = False
    start = False
    wptr  = 0
    w     = 0
    for dword_a in range(a, al):
        #print(hex(dword_a))
        if start: # start of new completition boundary part
            #    print("start")
            w_arr.append(w)
            wptr = 0
            w    = 0
            start = False

        w |= 1 << wptr

        if ((dword_a + 1) & (RCBS - 1)) == 0: # end of completition boundary part
            #    print("end")
            start = True
            if u_start:
                u_start = False
                if RCB == 1 and len(w_arr) == 0:
                    w_arr.append(w)
                    wptr = 0
                    w    = 0
        else:
            wptr += 1
            if wptr == DOWN_REG_SIZE * DOWN_REGIONS: # word overflow
                #        print("overflow")
                w_arr.append(w)
                w = 0
                wptr = 0

    o = False
    if u_start:
        u_start = False
        if RCB == 1:
            w_arr.append(w)
            if len(w_arr) == 1:
                w_arr.append(0)
            wptr = 0
            w    = 0
            o = True

    if w:
        w_arr.append(w)

    if RCB == 1:
        if (not o and (((dword_a + 1) & (RCBS - 1)) != 0) and RCB == 1
                and (al & (RCBS - 1)) <= RCBS // 2): # unaligned end
            w_arr.append(0)

    while (len(w_arr) < 4):
        w_arr.append(0)

    print_word_bitmaps(w_arr)
    return len(w_arr)


# algorithm used in hardware
def words_count_short(a, s):
    s = 0
    log = ""

    addr_u = a >> 2
    log += "addr_u: " + hex(addr_u) + "\n"
    addr_u_rcbs = (addr_u & (RCBS - 1))
    log += "addr_u_rcbs: " + hex(addr_u_rcbs) + "\n"
    addr_u_w = (addr_u % DOWN_W_D)
    log += "addr_u_w: " + hex(addr_u_w) + "\n"

    len_u = s
    log += "len_u: " + hex(len_u) + "\n"
    len_u_rcbs = (len_u & (RCBS - 1))
    log += "len_u_rcbs: " + hex(len_u_rcbs) + "\n"

    end_addr_u = addr_u_rcbs + len_u_rcbs
    log += "end_addr_u: " + hex(end_addr_u) + "\n"
    end_addr_u_rcbs = (end_addr_u & (RCBS - 1))
    log += "end_addr_u_rcbs: " + hex(end_addr_u_rcbs) + "\n"
    len_rest_u = len_u - (RCBS - addr_u_rcbs) - end_addr_u_rcbs
    log += "len_rest_u: " + hex(len_rest_u) + "\n"

    addr_u_rcbs_rounddown = (addr_u_rcbs // DOWN_W_D) * DOWN_W_D
    log += "addr_u_rcbs_rounddown: " + hex(addr_u_rcbs_rounddown) + "\n"
    words_in_first_rcbs_u = (RCBS - (addr_u_rcbs_rounddown)) // DOWN_W_D
    log += "words_in_first_rcbs_u: " + hex(words_in_first_rcbs_u) + "\n"
    words_in_last_rcbs_u  = ((end_addr_u_rcbs + DOWN_W_D - 1) // DOWN_W_D)
    log += "words_in_last_rcbs_u: " + hex(words_in_last_rcbs_u) + "\n"

    if addr_u_rcbs == 0: # aligned address
        log += "aligned address\n"
        if end_addr_u_rcbs == 0: # aligned end
            log += "aligned end\n"
            s = len_u >> DOWN_W_L
        else: # unaligned end
            log += "unaligned end\n"
            s = ((len_u - end_addr_u_rcbs) >> DOWN_W_L)
            s += words_in_last_rcbs_u
    else: # unaligned address
        log += "unaligned address\n"
        if (len_u >> RCBL) == 0 and (end_addr_u & RCBS) == 0: # unaligned in one RCBS
            log += "unaligned fit\n"
            s = (len_u + DOWN_W_D - 1) // DOWN_W_D
        elif end_addr_u_rcbs == 0: # aligned end
            log += "aligned end\n"
            s = words_in_first_rcbs_u
            s += len_rest_u >> DOWN_W_L
        else: # unaligned end
            log += "unaligned end\n"
            s = words_in_first_rcbs_u
            s += len_rest_u >> DOWN_W_L
            s += words_in_last_rcbs_u
    return (s, log)


# Checks the correctness of given transcript file with WORDS_COUNT_INFO logs.
#
# The format of accepted info log lines is as follows:
#
# <LINE>             -> # time: <time> :WORDS_COUNT_INFO:<INFO>
# <INFO>             -> <RCB_INFO>
# <INFO>             -> <REGIONS_INFO>
# <INFO>             -> <REG_SIZE_INFO>
# <INFO>             -> <TRANSACTION_INFO>
# <RCB_INFO>         -> RCB=<num>
# <REGIONS_INFO>     -> REGIONS=<num>
# <REG_SIZE_INFO>    -> REG_SIZE=<num>
# <TRANSACTION_INFO> -> <ADDR>,<LEN>,<MAX_WORDS>
# <ADDR>             -> trans_addr=0x<hex_num>
# <LEN>              -> trans_len=0x<hex_num>
# <MAX_WORDS>        -> trans_max_words_num=0x<hex_num>
#
# where <num> and <hex_num> are values used by the function
def check_transcript(transcript_file_name):
    # check file name
    if not os.path.isfile(transcript_file_name):
        print("Cannot find file " + transcript_file_name)
        return

    # import all globals
    global DOWN_REGIONS, DOWN_REG_SIZE
    global UP_ADDR_WIDTH, UP_LEN_WIDTH
    global DOWN_W_D, DOWN_W_L, REG_SIZE_L
    global REGS_L, RCB, RCBS, RCBL

    # start reading the transcript file
    all_ok = True
    with open(transcript_file_name, "r") as trans_file:
        for i, line in enumerate(trans_file):
            if (i + 1) % 100000 == 0:
                print("... transcript line: " + str(i + 1) + " ...")

            l_s0 = line.split(":")

            if len(l_s0) > 3 and l_s0[2] == "WORDS_COUNT_INFO": # detect INFO line
                l_s1 = l_s0[3].split(",")
                for e in range(len(l_s1)):
                    l_s1[e] = l_s1[e].split("=")

                if l_s1[0][0] == "RCB":
                    RCB = int(l_s1[0][1])

                    # recount secondary globals
                    RCBS = 64 // 4 if RCB == 0 else 128 // 4
                    RCBL = int(math.log(RCBS, 2))

                if l_s1[0][0] == "REGIONS":
                    DOWN_REGIONS = int(l_s1[0][1])

                    # recount secondary globals
                    DOWN_W_D = DOWN_REGIONS * DOWN_REG_SIZE
                    DOWN_W_L = int(math.log(DOWN_REGIONS * DOWN_REG_SIZE, 2))
                    REG_SIZE_L = int(math.log(DOWN_REG_SIZE, 2))
                    REGS_L = int(math.log(DOWN_REGIONS, 2))

                if l_s1[0][0] == "REG_SIZE":
                    DOWN_REG_SIZE = int(l_s1[0][1])

                    # recount secondary globals
                    DOWN_W_D = DOWN_REGIONS * DOWN_REG_SIZE
                    DOWN_W_L = int(math.log(DOWN_REGIONS * DOWN_REG_SIZE, 2))
                    REG_SIZE_L = int(math.log(DOWN_REG_SIZE, 2))
                    REGS_L = int(math.log(DOWN_REGIONS, 2))

                if l_s1[0][0] == "ADDR_WIDTH":
                    UP_ADDR_WIDTH = int(l_s1[0][1])

                if l_s1[0][0] == "LEN_WIDTH":
                    UP_LEN_WIDTH = int(l_s1[0][1])

                if l_s1[0][0] == "trans_addr":
                    #                           (    time     ,     addr         ,        len       ,  max_words_num )
                    (t_time, t_addr, t_len, t_n) = (l_s0[1][1:-1], int(l_s1[0][1], 16), int(l_s1[1][1], 16), int(l_s1[2][1], 16))

                    (n_ref, log) = words_count_short(t_addr * 4, t_len) # hardware usable algorithm
                    if n_ref != t_n:
                        all_ok = False
                        print("Incorrect max_words_num found!")
                        print()
                        print("transcript line: " + str(i + 1))
                        print("simulation time: " + t_time)
                        print()
                        print("         logged addr: " + hex(t_addr) + " (address of a DWORD)")
                        print("       logged length: " + hex(t_len) + " B (" + str(t_len) + " B)")
                        print("logged max_words_num: " + str(t_n))
                        print()
                        n_long = words_count_long(t_addr * 4, t_len) # simulation
                        print(" long count result: " + str(n_long))
                        print("referential result: " + str(n_ref))
                        print()
                        print("referential log:")
                        print()
                        print(log)
                        if input("Continue checking? (Y/N) ") not in ("y", "Y"):
                            break

    print("Checking done.")
    if all_ok:
        print("Transcript info correct.")
    return


#################################################################
# transctipt correctness checking
if len(sys.argv) > 1:
    check_transcript(sys.argv[1])

# loop for checking of correctness between functions words_count_long and words_count_short
transactions = 0
for i in range(transactions):
    a = randint(0, 2**10) << 2
    s = randint(1, 2**7)
    print("  addr: " + hex(a))
    print("length: " + str(s))
    n0 = words_count_long(a, s) # simulation
    print(n0)
    (n1, log) = words_count_short(a, s) # hardware usable algorithm
    print(n1)
    if n0 != n1:
        print("ERROR")
        print(log)
        break
