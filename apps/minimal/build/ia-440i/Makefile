# Makefile: Makefile for card
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/bittware/ia-440i
APP_CONF = app_conf.tcl

PCIE_CONF ?= 1xgen5x8x8
export PCIE_CONF

OUTPUT_NAME = ia-440i-minimal-pcie$(PCIE_CONF)

.PHONY: all 400g1 # 100g2 25g8 10g8

all: 400g1

# TODO: add support for different ETH configurations
# 10g8: ETH_PORT_SPEED=10
# 10g8: ETH_PORT_CHAN=4
# 10g8: OUTPUT_NAME:=$(OUTPUT_NAME)-10g8
# 10g8: build
#
# 25g8: ETH_PORT_SPEED=25
# 25g8: ETH_PORT_CHAN=4
# 25g8: OUTPUT_NAME:=$(OUTPUT_NAME)-25g8
# 25g8: build
#
# 100g2: ETH_PORT_SPEED=100
# 100g2: ETH_PORT_CHAN=1
# 100g2: OUTPUT_NAME:=$(OUTPUT_NAME)-100g2
# 100g2: build

400g1: ETH_PORT_SPEED=400
400g1: ETH_PORT_CHAN=1
400g1: EHIP_PORT_TYPE=0
400g1: OUTPUT_NAME:=$(OUTPUT_NAME)-400g1
400g1: build

include $(CARD_BASE)/src/card.mk
