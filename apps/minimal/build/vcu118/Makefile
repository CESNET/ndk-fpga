# Makefile: Makefile for VCU118
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Vadislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/amd/vcu118
APP_CONF = app_conf.tcl

PCIE_CONF ?= 1xgen3x16
export PCIE_CONF

OUTPUT_NAME = vcu118-minimal-pcie$(PCIE_CONF)

ETH_PORT_SPEED=100
ETH_PORT_CHAN=1

.PHONY: all 100g2 100g0

all: 100g2

100g2: ETH_PORTS=2
100g2: OUTPUT_NAME:=$(OUTPUT_NAME)-100g2
100g2: build

100g0: ETH_PORTS=0
100g0: OUTPUT_NAME:=$(OUTPUT_NAME)-100g0
100g0: build

include $(CARD_BASE)/src/card.mk
