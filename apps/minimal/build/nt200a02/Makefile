# Makefile: Makefile for build the whole card design
# Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/napatech/nt200a02
APP_CONF = app_conf.tcl
OUTPUT_NAME = nt200a02-minimal

ETH_PORT_SPEED=100
ETH_PORT_CHAN=1

.PHONY: all 100g2

all: 100g2

100g2: ETH_PORTS=2
100g2: OUTPUT_NAME:=nt200a02-minimal-100g2
100g2: build

include $(CARD_BASE)/src/card.mk
