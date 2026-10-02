# Makefile: Makefile for run cocotb tests
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


CARD = n6010
TARGET = cocotb
TOP_LEVEL_ENT=fpga

CARD_DIR=../../build/$(CARD)/

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
# Shared register access classes (dram_pkt_capture_regs.py)
SCRIPTS_DIR:=$(realpath $(ROOT_DIR)/../../scripts)

all:
	make TARGET=$(TARGET) -C $(CARD_DIR) PYTHONPATH=$$PYTHONPATH:$(ROOT_DIR):$(SCRIPTS_DIR) TOP_LEVEL_ENT=$(TOP_LEVEL_ENT)

include ../../../../build/Makefile

