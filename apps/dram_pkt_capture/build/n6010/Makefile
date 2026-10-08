# Makefile: Makefile for card
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/silicom/n6010
APP_CONF = app_conf.tcl

PCIE_CONF ?= 1xgen4x16
export PCIE_CONF

OUTPUT_NAME = n6010-dram-pkt-capture-pcie$(PCIE_CONF)

.PHONY: all 100g2

all: 100g2

100g2: ETH_PORT_SPEED=100
100g2: ETH_PORT_CHAN=1
100g2: OUTPUT_NAME:=$(OUTPUT_NAME)-100g2
100g2: build

include $(CARD_BASE)/src/card.mk
