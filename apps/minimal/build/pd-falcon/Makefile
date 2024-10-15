# Makefile: Makefile for prodesign pd-falcon card
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Denis Kurka <xkurka05@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

# Set path to top-level of NDK-FPGA repository
COMBO_BASE = ../../../..
CARD_BASE = $(COMBO_BASE)/cards/prodesign/pd-falcon
APP_CONF = app_conf.tcl
OUTPUT_NAME = pd-falcon

.PHONY: all 100g2

all: 100g2

100g2: ETH_PORT_SPEED=100
100g2: ETH_PORT_CHAN=1
100g2: OUTPUT_NAME:=$(OUTPUT_NAME)-100g2
100g2: build

include $(CARD_BASE)/src/card.mk
