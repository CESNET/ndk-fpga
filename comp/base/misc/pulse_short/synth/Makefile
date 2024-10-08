# Makefile: Makefile script to compile specified module
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=PULSE_SHORT

SYNTH=vivado
export CLK_PERIOD=2.56
export DEVICE=ULTRASCALE


all: comp
# the way: ndk/common/build/Makefile
include ../../../../../build/Makefile
.PHONY: all
