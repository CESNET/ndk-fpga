# Makefile: Makefile for run cocotb tests
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


CARD = fb2cghh

CARD_DIR=../../build/$(CARD)/

all:
	make TARGET=cocotb -C $(CARD_DIR) PYTHONPATH=$$PYTHONPATH:$(PWD)
