# Makefile: Makefile for build the whole card design
# Copyright 2025 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/amd/alveo-v80
APP_CONF = app_conf.tcl

PCIE_CONF ?= 1xGen4x8

OUTPUT_NAME = alveo-v80-sparklev-pcie$(PCIE_CONF)

ETH_PORT_SPEED=100
ETH_PORT_CHAN=1

.PHONY: all 100g2

all: 100g2

100g2: ETH_PORTS=2
100g2: OUTPUT_NAME:=$(OUTPUT_NAME)-100g2
100g2: build

include $(CARD_BASE)/src/card.mk
