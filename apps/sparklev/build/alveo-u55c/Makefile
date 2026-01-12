# Makefile: Makefile for build the whole card design
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

# Set path to top-level of NDK-FPGA repository
CORE_BASE=../../../../core
CARD_BASE:=$(dir $(lastword $(MAKEFILE_LIST)))
APP_CONF=app_conf.tcl

PCIE_CONF=1xGen4x4
DMA_TYPE=4

USER_ENV?=

OUTPUT_NAME=alveo-u55c-sparklev-pcie$(PCIE_CONF)

.PHONY: all  

all: build 

include $(CORE_BASE)/core.mk
