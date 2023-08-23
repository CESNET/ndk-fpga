# Makefile: Makefile for XpressSX AGI-FH400G card
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal cabal@cesnet.cz
#           Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

COMBO_BASE = ../..
CARD_BASE = $(COMBO_BASE)/ndk/cards/agi-fh400g
APP_CONF = app_conf.tcl

ifndef BOARD_REV
BOARD_REV = 0
endif

ifeq ($(BOARD_REV),0)
OUTPUT_NAME = agi-fh400g-minimal
else
OUTPUT_NAME = agi-fh400g-minimal-rev$(BOARD_REV)
endif

.PHONY: all 1x400g-8 2x200g-4 4x100g-2 8x50g-1 2x40g-4 8x25g-1 8x10g-1 mr_2x100g-4 mr_8x25g-1_8x10g-1

all: 400g1

10g8   : ETH_PORT_SPEED=10
10g8   : ETH_PORT_CHAN=8
10g8   : OUTPUT_NAME:=$(OUTPUT_NAME)-10g8
10g8   : EHIP_PORT_TYPE=0
10g8   : build
8x10g-1: 10g8

25g8   : ETH_PORT_SPEED=25
25g8   : ETH_PORT_CHAN=8
25g8   : OUTPUT_NAME:=$(OUTPUT_NAME)-25g8
25g8   : EHIP_PORT_TYPE=0
25g8   : build
8x25g-1: 25g8

40g2   : ETH_PORT_SPEED=40
40g2   : ETH_PORT_CHAN=2
40g2   : OUTPUT_NAME:=$(OUTPUT_NAME)-40g2
40g2   : EHIP_PORT_TYPE=0
40g2   : build
2x40g-4: 40g2

50g8   : ETH_PORT_SPEED=50
50g8   : ETH_PORT_CHAN=8
50g8   : OUTPUT_NAME:=$(OUTPUT_NAME)-50g8
50g8   : EHIP_PORT_TYPE=0
50g8   : build
8x50g-1: 50g8

100g4   : ETH_PORT_SPEED=100
100g4   : ETH_PORT_CHAN=4
100g4   : OUTPUT_NAME:=$(OUTPUT_NAME)-100g4
100g4   : EHIP_PORT_TYPE=0
100g4   : build
4x100g-2: 100g4

100g2   : ETH_PORT_SPEED=100
100g2   : ETH_PORT_CHAN=2
100g2   : OUTPUT_NAME:=$(OUTPUT_NAME)-100g2
100g2   : EHIP_PORT_TYPE=0
100g2   : build
2x100g-4: 100g2

200g2   : ETH_PORT_SPEED=200
200g2   : ETH_PORT_CHAN=2
200g2   : OUTPUT_NAME:=$(OUTPUT_NAME)-200g2
200g2   : EHIP_PORT_TYPE=0
200g2   : build
2x200g-4: 200g2

400g1   : ETH_PORT_SPEED=400
400g1   : ETH_PORT_CHAN=1
400g1   : OUTPUT_NAME:=$(OUTPUT_NAME)-400g1
400g1   : EHIP_PORT_TYPE=0
400g1   : build
1x400g-8: 400g-1

mr_2x100g-4: ETH_PORT_SPEED=100
mr_2x100g-4: ETH_PORT_CHAN=2
mr_2x100g-4: OUTPUT_NAME:=$(OUTPUT_NAME)-100g2mr
mr_2x100g-4: EHIP_PORT_TYPE=1
mr_2x100g-4: build
100g2mr    : mr_2x100g-4

mr_8x25g-1_8x10g-1: ETH_PORT_SPEED=25
mr_8x25g-1_8x10g-1: ETH_PORT_CHAN=8
mr_8x25g-1_8x10g-1: OUTPUT_NAME:=$(OUTPUT_NAME)-25g10g8mr
mr_8x25g-1_8x10g-1: EHIP_PORT_TYPE=1
mr_8x25g-1_8x10g-1: build
25g10g8mr         : mr_8x25g-1_8x10g-1

include $(CARD_BASE)/src/card.mk
