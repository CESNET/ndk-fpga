# Makefile: cocotb verification of HBM_TESTER
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# The test-only wrapper gives every HBM port its own AXI signals for the cocotbext-axi memory models.
# TOP_LEVEL_PATH selects this directory's Modules.tcl.
TOP_LEVEL_ENT=HBM_TESTER_TB_WRAPPER
TOP_LEVEL_PATH=.
TARGET=nvc-sim
NVC_PLATFORM_TAGS := xilinx
# An RTL assertion must fail the run, not only print an error.
NVC_EXIT_SEVERITY := error

# HBM_TESTER indexes its counter registers with MI_ADDR(8 downto 4), so the bench keeps that field below PORTS.
PORTS          ?= 4
AXI_DATA_WIDTH ?= 256
CNT_WIDTH      ?= 14
NVC_ELAB_ARGS += -g PORTS=$(PORTS) -g AXI_DATA_WIDTH=$(AXI_DATA_WIDTH) -g CNT_WIDTH=$(CNT_WIDTH)

.PHONY: all
all: comp

include ../../../../../build/Makefile
