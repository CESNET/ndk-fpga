# Makefile: Makefile script to compile specified module
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=JTAG_OP_CLIENT

#SYNTH=quartus
export CLK_PERIOD=4.0

all: comp
include ../../../../build/Makefile
.PHONY: all clean

clean:
	find . -not -name 'Makefile' -type f -exec rm -f {} +
	find . -not -name '.*' -type d -exec rm -rf {} +
