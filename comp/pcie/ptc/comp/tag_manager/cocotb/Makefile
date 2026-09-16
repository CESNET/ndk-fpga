# Makefile: Makefile to compile module
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=PTC_TAG_MANAGER
TARGET=cocotb

# `make` alone uses the entity defaults of PTC_TAG_MANAGER. Run the combinations
# from ver_settings.py through multi_ver_cocotb.py, or set GENERICS directly:
# make GENERICS="-gPCIE_TAG_WIDTH=8 -gCHECK_CPL_CREDITS=True -gEXTRA_WORDS=8"
.PHONY: all
all: comp

include ../../../../../../build/Makefile
