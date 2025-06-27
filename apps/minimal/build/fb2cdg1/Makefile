# Makefile: Makefile for Silicom ThunderFjord fb2cdg1 card
# Copyright (C) 2025 DynaNIC Semiconductors Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/silicom/fb2cdg1
APP_CONF = app_conf.tcl

PCIE_CONF ?= 1xgen5x8x8
export PCIE_CONF

OUTPUT_NAME = fb2cdg1-minimal-pcie$(PCIE_CONF)

.PHONY: all 400g2

all: 400g2

400g2: ETH_PORTS=2
400g2: ETH_PORT_SPEED=400
400g2: ETH_PORT_CHAN=1
400g2: EHIP_PORT_TYPE=0
400g2: OUTPUT_NAME:=$(OUTPUT_NAME)-400g2
400g2: build

include $(CARD_BASE)/src/card.mk
