# Makefile: Makefile for card
# Copyright (C) BrnoLogic, Ltd. - All Rights Reserved
# Author: Tomas Fukac <fukac@brnologic.com>, May 2024
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/silicom/n5014
APP_CONF = app_conf.tcl

PCIE_CONF ?= 1xgen4x16
export PCIE_CONF

OUTPUT_NAME = n5014-minimal-pcie$(PCIE_CONF)

.PHONY: all 100g4

all: 100g4

100g4: ETH_PORT_SPEED=100
100g4: ETH_PORT_CHAN=1
100g4: OUTPUT_NAME:=$(OUTPUT_NAME)-100g4
100g4: build

include $(CARD_BASE)/src/card.mk
