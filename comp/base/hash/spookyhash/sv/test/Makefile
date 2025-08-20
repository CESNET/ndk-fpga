# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Makefile for running test SystemVerilog implementation
# of spookyhash in spookyhash.sv

# 'make' buils all necessary files.
# 'make run' builds all necessary files and runs simulation of testbench.sv with the specified key width.
# 'make test' runs pytest test executing the simulation for key lengths ranging from 1B to 191B.

TOP_LEVEL=testbench
TESTBENCH=testbench.sv
MTI_HOME=/usr/local/fpga/modelsim/2024.1/questasim
CC=g++
CFLAGS=-shared -fPIC -I. -I${MTI_HOME}/include -I../../sw
SVC=vlog
SVC_FLAGS=-sv
SIM=vsim
SIM_FLAGS=-c -sv_lib spooky_cextern -do "run -all; quit"

KEY_WIDTH=40 # passed to testbench.sv package

all: testbench spooky_cextern.so

run: testbench spooky_cextern.so
	$(SIM) $(SIM_FLAGS) $(TOP_LEVEL)

test: testbench spooky_cextern.so test.py
	pytest test.py

testbench: $(TESTBENCH) spookyhash
	$(SVC) $(SVC_FLAGS) $< +define+KEY_WIDTH=${KEY_WIDTH}

spookyhash: ../spookyhash.sv
	$(SVC) $(SVC_FLAGS) $^

spooky_cextern.so: spooky_cextern.cpp ../../sw/SpookyV2.cpp spooky_dpi.h
	${CC} ${CFLAGS} $^ -o $@

spooky_dpi.h: $(TESTBENCH)
	$(SVC) $(SVC_FLAGS) -dpiheader spooky_dpi.h $(TESTBENCH) +define+KEY_WIDTH=${KEY_WIDTH}

clean:
	@rm -r spooky_cextern.so spooky_dpi.h transcript work test_logs __pycache__
