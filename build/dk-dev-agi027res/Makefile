# Makefile: Makefile for DK-DEV-AGI027RES card
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal cabal@cesnet.cz
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

COMBO_BASE = ../..
CARD_BASE = $(COMBO_BASE)/ndk/cards/dk-dev-agi027res
APP_CONF = app_conf.tcl
OUTPUT_NAME = dk-dev-agi027res-minimal

.PHONY: all 400g1 200g2 100g4 50g8 40g2 25g8 10g8

all: 400g1

10g8: ETH_PORT_SPEED=10
10g8: ETH_PORT_CHAN=8
10g8: OUTPUT_NAME:=$(OUTPUT_NAME)-10g8
10g8: build

25g8: ETH_PORT_SPEED=25
25g8: ETH_PORT_CHAN=8
25g8: OUTPUT_NAME:=$(OUTPUT_NAME)-25g8
25g8: build

40g2: ETH_PORT_SPEED=40
40g2: ETH_PORT_CHAN=2
40g2: OUTPUT_NAME:=$(OUTPUT_NAME)-40g2
40g2: build

50g8: ETH_PORT_SPEED=50
50g8: ETH_PORT_CHAN=8
50g8: OUTPUT_NAME:=$(OUTPUT_NAME)-50g8
50g8: build

100g4: ETH_PORT_SPEED=100
100g4: ETH_PORT_CHAN=4
100g4: OUTPUT_NAME:=$(OUTPUT_NAME)-100g4
100g4: build

200g2: ETH_PORT_SPEED=200
200g2: ETH_PORT_CHAN=2
200g2: OUTPUT_NAME:=$(OUTPUT_NAME)-200g2
200g2: build

400g1: ETH_PORT_SPEED=400
400g1: ETH_PORT_CHAN=1
400g1: OUTPUT_NAME:=$(OUTPUT_NAME)-400g1
400g1: build

include $(CARD_BASE)/src/card.mk
