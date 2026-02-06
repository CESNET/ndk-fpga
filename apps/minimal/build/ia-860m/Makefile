# Makefile: Makefile for Bittware IA-860m
# Copyright (C) 2025 DynaNIC Semiconductors Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/bittware/ia-860m
APP_CONF = app_conf.tcl

BOARD_VARIANT ?= 0
export BOARD_VARIANT

PCIE_CONF ?= 1xgen5x8x8
export PCIE_CONF

OUTPUT_NAME = ia-860m-minimal-pcie$(PCIE_CONF)

.PHONY: all 400g2

all: 400g2

# For minimal use only 2 port design
# 3 port design is currently uncompatible with minimal application core
400g2: ETH_PORTS=2
400g2: ETH_PORT_SPEED=400
400g2: ETH_PORT_CHAN=1
400g2: EHIP_PORT_TYPE=0
400g2: OUTPUT_NAME:=$(OUTPUT_NAME)-400g2
400g2: build

400g3: ETH_PORTS=3
400g3: ETH_PORT_SPEED=400
400g3: ETH_PORT_CHAN=1
400g3: EHIP_PORT_TYPE=0
400g3: OUTPUT_NAME:=$(OUTPUT_NAME)-400g3
400g3: build

include $(CARD_BASE)/src/card.mk
