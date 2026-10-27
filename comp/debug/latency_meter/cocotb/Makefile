# Makefile: Makefile to run the cocotb test of the LATENCY_METER
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

TOP_LEVEL_ENT=LATENCY_METER
TARGET=cocotb

.PHONY: all
all: comp

# Without GENERICS, as multi_ver_cocotb.py gives them, a run takes the "default" setting of ver_settings.py.
include ../../../../build/scripts/multi_ver/ver_settings.mk

include ../../../../build/Makefile
