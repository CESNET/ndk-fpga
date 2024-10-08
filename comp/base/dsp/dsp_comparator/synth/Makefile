# Makefile: Makefile script to compile specified module
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=DSP_COMPARATOR

SYNTH=quartus
#export CLK_PERIOD=4.0
# default DEVICE is STRATIX10, uncomment following line to use AGILEX
export DEVICE=AGILEX

all: comp
include ../../../../../build/Makefile
.PHONY: all
