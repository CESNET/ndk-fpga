# Makefile: Makefile for XpressSX AGI-FH400G card
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal cabal@cesnet.cz
#           Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

COMBO_BASE = ../..
CARD_BASE = $(COMBO_BASE)/ndk/cards/agi-fh400g
APP_CONF = app_conf.tcl

ifeq ($(BOARD_REV),0)
OUTPUT_NAME = agi-fh400g-minimal
else
OUTPUT_NAME = agi-fh400g-minimal-rev$(BOARD_REV)
endif

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
