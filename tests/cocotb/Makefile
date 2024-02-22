# Makefile: Makefile for run cocotb tests
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


CARD = fb2cghh
SIM = cocotb

CARD_DIR=../../build/$(CARD)/

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

all:
	make TARGET=$(SIM) -C $(CARD_DIR) PYTHONPATH=$$PYTHONPATH:$(ROOT_DIR) TOP_LEVEL_ENT=fpga
