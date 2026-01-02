# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Makefile for running test SystemVerilog implementation
# of SipHash and HalfSipHash in siphash.sv

# 'make' buils all necessary files.
# 'make run' builds all necessary files and runs simulation of testbench.sv with the specified key width.
# 'make test' runs pytest test executing the simulation for key lengths ranging from 1B to 191B.

TOP_LEVEL=testbench
TESTBENCH=testbench.sv
MTI_HOME=$(dir $(shell which vsim))..
HASH_NAME=siphash
CPP=../../sw/siphash.cpp
CEXTERN=${HASH_NAME}_cextern
DPI=${HASH_NAME}_dpi.h

CC=g++
CFLAGS=-shared -fPIC -I. -I${MTI_HOME}/include -I../../sw
SVC=vlog
SVC_FLAGS=-sv
SIM=vsim
SIM_FLAGS=-c -sv_lib ${CEXTERN} -do "run -all; quit"

KEY_WIDTH=40 # passed to testbench.sv package

all: ${TOP_LEVEL} ${CEXTERN}.so

run: ${TOP_LEVEL} ${CEXTERN}.so
	${SIM} ${SIM_FLAGS} ${TOP_LEVEL}

test: ${TOP_LEVEL} ${CEXTERN}.so test.py
	python3 -m venv test_venv; \
	. test_venv/bin/activate;  \
	pip install pytest;        \
	pytest test.py;            \
	rm -fr test_venv

${TOP_LEVEL}: ${TESTBENCH} ${HASH_NAME}
	${SVC} ${SVC_FLAGS} $< +define+KEY_WIDTH=${KEY_WIDTH}

${HASH_NAME}: ../${HASH_NAME}.sv
	${SVC} ${SVC_FLAGS} $^

${CEXTERN}.so: ${CEXTERN}.cpp ${CPP} ${DPI}
	${CC} ${CFLAGS} $^ -o $@

${DPI}: ${TESTBENCH}
	${SVC} ${SVC_FLAGS} -dpiheader ${DPI} ${TESTBENCH} +define+KEY_WIDTH=${KEY_WIDTH}

clean:
	@rm -r ${CEXTERN}.so ${DPI} transcript work test_logs __pycache__
