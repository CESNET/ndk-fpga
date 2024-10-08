# Makefile: Makefile to compile module
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=TX_MAC_LITE_CMAC
#SYNTH=quartus

CLK_PORTS=MI_CLK TX_CLK RX_CLK RX_CLK_X2
CLK_PERIOD=5 3.106 5 2.5
export DEVICE=ULTRASCALE

.PHONY: all
all: comp

include ../../../../../../../build/Makefile
