# Makefile: cocotb verification of HBM_TESTER_MON
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

TOP_LEVEL_ENT=HBM_TESTER_MON
TARGET=cocotb
NVC_PLATFORM_TAGS := xilinx
# An RTL assertion must fail the run, not only print an error.
NVC_EXIT_SEVERITY := error

.PHONY: all
all: comp

# Without GENERICS, as multi_ver_cocotb.py gives them, a run takes the "default" setting of ver_settings.py.
include ../../../../../build/scripts/multi_ver/ver_settings.mk

include ../../../../../build/Makefile
