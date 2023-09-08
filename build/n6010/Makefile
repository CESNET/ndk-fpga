# Makefile: Makefile for card
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Usage of the configuration parameters in this file is described
# in the Parametrization section of the NDK-CORE documentation.

COMBO_BASE = ../..
CARD_BASE = $(COMBO_BASE)/ndk/cards/silicom/n6010
APP_CONF = app_conf.tcl
OUTPUT_NAME = n6010-minimal

.PHONY: all 100g2 25g8 10g8

all: 100g2

10g8: ETH_PORT_SPEED=10
10g8: ETH_PORT_CHAN=4
10g8: OUTPUT_NAME:=$(OUTPUT_NAME)-10g8
10g8: build

25g8: ETH_PORT_SPEED=25
25g8: ETH_PORT_CHAN=4
25g8: OUTPUT_NAME:=$(OUTPUT_NAME)-25g8
25g8: build

100g2: ETH_PORT_SPEED=100
100g2: ETH_PORT_CHAN=1
100g2: OUTPUT_NAME:=$(OUTPUT_NAME)-100g2
100g2: build

include $(CARD_BASE)/src/card.mk
