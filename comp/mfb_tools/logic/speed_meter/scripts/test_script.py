#!/usr/bin/env python3

import sys
import os
import nfb
import csv

# TODO: argument parser
args = []
args = sys.argv[1:]

dev = nfb.NFBDevice()
comp = dev.getComp("netcope,bus,mi", 0)

# Speed meter clock frequency
sm_clk_freq = 200000000 # 200 MHz

# Define min and max frame sizes (in bytes)
min_fr_size = 64
max_fr_size = 1526
fr_size_step = 4

# List of frame lengths for TX generator(s)
fr_lengths = []
fr_lengths = list(range(min_fr_size, max_fr_size, fr_size_step))

# Open CSV file to save data
if len(args) == 0:
    print("Supply argument (100g1, 25g4, ...)")
    exit()
elif args[0] == "100g1":
    f = open('./100g1_speed.csv', 'w', newline='')
elif args[0] == "25g4":
    f = open('./25g4_speed.csv', 'w', newline='')
elif args[0] == "10g4":
    f = open('./10g4_speed.csv', 'w', newline='')
else:
    print("Incorrect speed!")
    #print("Options for F-tile arch: 400g1, 200g2, 100g4, 50g8, 40g2, 25g8, 10g8") TODO
    print("Options for E-tile arch: 100g1, 25g4, 10g4")
    exit()

writer = csv.writer(f)

# CSV file row (length, speed0, speed1)
row = ["Length", "RX0 speed", "RX1 speed"]
writer.writerow(row)

# Enable MACs
os.system('nfb-eth -e 1')

# Reset MAC counters
os.system('nfb-eth -R')

# Reset TX generator(s)
comp.write32(0x00005180, 0x10)
comp.write32(0x00005280, 0x10)

# Reset TX speed meter
comp.write32(0x0000512C, 0x1)
comp.write32(0x0000522C, 0x1)

# Set mux input to make the TX generator the source of data
comp.write32(0x0000510C, 0x1)
comp.write32(0x0000520C, 0x1)

for i in range(len(fr_lengths)):

    # Reset TX speed meter
    comp.write32(0x0000512C, 0x1)
    comp.write32(0x0000522C, 0x1)

    length = fr_lengths[i]
    print("Length: " + str(length))

    # Set frame length of TX generator(s)
    comp.write32(0x00005184, length - 4)
    print("Actual generator length: " + str(comp.read32(0x00005184))) # a quick check of written length
    comp.write32(0x00005284, length - 4)

    # Start TX generator(s)
    comp.write32(0x00005180, 0x1)
    comp.write32(0x00005280, 0x1)

    # -------------------------------------------
    # Retrieve results from speed meter 0
    drd = 0
    # Check if speed meter 0 is done
    while drd != 1:
        drd = comp.read32(0x00005124)

    # Retrieve results from speed meter 1
    drd = 0
    # Check if speed meter 1 is done
    while drd != 1:
        drd = comp.read32(0x00005224)

    # Stop TX generator(s)
    comp.write32(0x00005180, 0x0)
    comp.write32(0x00005280, 0x0)

    # -------------------------------------------
    # Speed meter 0
    drd = comp.read32(0x00005128) * 8 / (10**9) # read accumulated bytes and convert to Gigabits
    sm_ticks = comp.read32(0x00005120) # read number of ticks until the speed meter reached max values
    sm_run_time = sm_ticks / sm_clk_freq
    sm0_speed = round(drd / sm_run_time, 2)
    print("Speed meter 0 data: " + str(sm0_speed) + " [Gbps]")

    # -------------------------------------------
    # Speed meter 1
    drd = comp.read32(0x00005228) * 8 / (10**9) # read accumulated bytes and convert to Gigabits
    sm_ticks = comp.read32(0x00005220) # read number of ticks until the speed meter reached max values
    sm_run_time = sm_ticks / sm_clk_freq
    sm1_speed = round(drd / sm_run_time, 2)
    print("Speed meter 1 data: " + str(sm1_speed) + " [Gbps]")

    # -------------------------------------------
    # Save row to CSV file
    row = [str(length), str(sm0_speed), str(sm1_speed)]
    writer.writerow(row) # write data to CSV file

f.close()

#print MAC stats
os.system('nfb-eth')
