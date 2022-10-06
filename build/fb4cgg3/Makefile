# Makefile: Makefile for fb4cgg3/fb2cgg3 card
# Copyright (C) 2022 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

COMBO_BASE = ../..
CARD_BASE = $(COMBO_BASE)/ndk/cards/fb4cgg3
APP_CONF = app_conf.tcl
OUTPUT_NAME = fb4cgg3-minimal

.PHONY: all 100g2 100g4

all: 100g2

100g2: ETH_PORTS=2
100g2: ETH_PORT_SPEED=100
100g2: ETH_PORT_CHAN=1
100g2: OUTPUT_NAME:=fb2cgg3-minimal-100g2
100g2: build

100g4: ETH_PORTS=4
100g4: ETH_PORT_SPEED=100
100g4: ETH_PORT_CHAN=1
100g4: OUTPUT_NAME:=$(OUTPUT_NAME)-100g4
100g4: build

include $(CARD_BASE)/src/card.mk
