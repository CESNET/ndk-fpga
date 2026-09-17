# Makefile: Makefile to compile module
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=PCIE_TELEMETRY_MI
TARGET=cocotb

# A short drain period keeps the simulation short, the testbench reads the value
# back from the configuration registers.
TB_GENERICS ?= -gDRAIN_PERIOD=2048 -gPCIE_ENDPOINTS=2 -gDMA_PORTS=2
NVC_ELAB_FLAGS = -O3 $(TB_GENERICS)

.PHONY: all
all: comp

include ../../../../../build/Makefile
