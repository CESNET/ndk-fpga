# Makefile: Makefile to compile module
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=PTC_STORAGE_FIFO
TARGET=cocotb

# `make` alone uses PTC_STORAGE_FIFO's own entity defaults, which already match
# the real R-Tile x16 instantiation (MFB_REGIONS=4, MFB_REG_SIZE=1,
# MFB_BLOCK_SIZE=4, MFB_ITEM_WIDTH=32, MVB_ITEMS=4, MAIN_FIFO_ITEMS=512).
# A smaller MAIN_FIFO_ITEMS (to hit FIFO full/empty corners faster) can be set
# by hand, e.g.: make GENERICS="-gMAIN_FIFO_ITEMS=16".
.PHONY: all
all: comp

include ../../../../../../build/Makefile
