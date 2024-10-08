# Makefile: Makefile to compile module
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=TX_MAC_LITE_UMII
SYNTH=quartus

CLK_PORTS=MI_CLK MII_CLK RX_CLK RX_CLK_X2
CLK_PERIOD=5 3.9 5 2.5
#export DEVICE=ULTRASCALE

all: comp
include ../../../../../../../build/Makefile
.PHONY: all
