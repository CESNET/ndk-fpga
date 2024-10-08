# card.mk: Makefile include
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
# 			Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Mandatory parameters (needs to be set in user Makefile)
###############################################################################

# Load correct paths to build system
include $(COMBO_BASE)/conf/ndk_paths.mk

# Optional parameters (can be changed in user Makefile)
###############################################################################

# Name for output files (rootname)
# This value is set as default in SYNTH_FLAGS(OUTPUT)
OUTPUT_NAME ?= fb2cghh

USER_ENV ?=

# Private parameters (do not change these values in user Makefile)
###############################################################################

# Get directory of this Makefile.inc
CARD_BASE_LOCAL := $(dir $(lastword $(MAKEFILE_LIST)))
CARD_BASE ?= $(CARD_BASE_LOCAL)/..
CORE_BASE ?= $(COMBO_BASE)/ndk/core/intel

NETCOPE_ENV = \
	OFM_PATH=$(OFM_PATH)\
	COMBO_BASE=$(COMBO_BASE)\
	FIRMWARE_BASE=$(FIRMWARE_BASE)\
	CARD_BASE=$(CARD_BASE) \
	CORE_BASE=$(CORE_BASE) \
	APP_CONF=$(APP_CONF) \
	OUTPUT_NAME=$(OUTPUT_NAME) \
	ETH_PORTS=$(ETH_PORTS) \
	ETH_PORT_SPEED=$(ETH_PORT_SPEED) \
	ETH_PORT_CHAN=$(ETH_PORT_CHAN) \
	DMA_TYPE=$(DMA_TYPE) \
	$(USER_ENV)

include $(CORE_BASE)/core.mk
include $(OFM_PATH)/build/Makefile.Vivado.inc
