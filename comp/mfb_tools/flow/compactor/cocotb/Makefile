# Makefile: Makefile to compile module
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=MFB_COMPACTOR
TARGET=cocotb

# `make` alone uses MFB_COMPACTOR's own entity defaults (REGIONS=4,
# REGION_SIZE=1, BLOCK_SIZE=8, ITEM_WIDTH=32, META_WIDTH=0, FLUSH_TIMEOUT=8,
# USE_PIPE=true, FWFT_MODE=true), matching the reference instance behind the
# R-Tile PCIe HIP AXI->MFB converter. Other generic corners (REGION_SIZE>1,
# META_WIDTH>0, USE_PIPE=False, FLUSH_TIMEOUT=0, FWFT_MODE=False) are covered
# by ver_settings.py, e.g.:
#   make GENERICS="-gREGION_SIZE=2"
# or run the whole sweep with multi_ver_cocotb.py (see ver_settings.py).
.PHONY: all
all: comp

include ../../../../../build/Makefile
