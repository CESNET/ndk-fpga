# Makefile: cocotb verification of HBM_TESTER_MON
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

TOP_LEVEL_ENT=HBM_TESTER_MON
TARGET=nvc-sim
NVC_PLATFORM_TAGS := xilinx
# An RTL assertion must fail the run, not only print an error.
NVC_EXIT_SEVERITY := error

# Narrow counters reach their saturation in a short window; the bench reads the width from the ports.
CNT_WIDTH ?= 8
NVC_ELAB_ARGS += -g CNT_WIDTH=$(CNT_WIDTH)

.PHONY: all
all: comp

include ../../../../../build/Makefile
