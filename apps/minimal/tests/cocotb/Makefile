# Makefile: Makefile for run cocotb tests
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


CARD = fb2cghh
TARGET = cocotb
TOP_LEVEL_ENT=fpga

CARD_DIR=../../build/$(CARD)/

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

all:
	make TARGET=$(TARGET) -C $(CARD_DIR) PYTHONPATH=$$PYTHONPATH:$(ROOT_DIR) TOP_LEVEL_ENT=$(TOP_LEVEL_ENT)

.PHONY: issues issue1 issue2

issues:
	make COCOTB_MODULE=$(COCOTB_MODULE) TARGET=$(TARGET) -C $(CARD_DIR) PYTHONPATH=$$PYTHONPATH:$(ROOT_DIR) TOP_LEVEL_ENT=$(TOP_LEVEL_ENT)

issue1:
	make issues COCOTB_MODULE=issues.$@ CARD=n6010
issue2:
	make issues COCOTB_MODULE=issues.$@ CARD=n6010

include ../../../../build/Makefile

