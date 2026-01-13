# core.mk: Common Makefile for all cards
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# This value is set as default in SYNTH_FLAGS(OUTPUT)
OUTPUT_NAME?=unknown-card
USER_ENV ?=

CORE_BASE?=$(dir $(lastword $(MAKEFILE_LIST)))

PCIE_CONF?=1xGen3x16

ETH_PORTS?=1
ETH_PORT_SPEED?=100
ETH_PORT_CHAN?=1

# Supported DMA types (possible values: 0, 3, 4):
# 0 - Disable DMA
# 3 - DMA Medusa
# 4 - DMA Calypte
DMA_TYPE?=3

# Enables debug components of a DMA module
DMA_DEBUG_ENABLE?=false
NET_MOD_ENABLE?=true
APP_CORE_ENABLE?=true
BMC_ENABLE?=true
USR_CORE_ARCH?=FULL

include $(CORE_BASE)/ndk_paths.mk

NETCOPE_ENV += \
	OFM_PATH=$(OFM_PATH) \
	COMBO_BASE=$(COMBO_BASE) \
	FIRMWARE_BASE=$(FIRMWARE_BASE) \
	CARD_BASE=$(CARD_BASE) \
	CORE_BASE=$(CORE_BASE) \
	APP_CONF=$(APP_CONF) \
	OUTPUT_NAME=$(OUTPUT_NAME) \
	ETH_PORTS=$(ETH_PORTS) \
	ETH_PORT_SPEED=$(ETH_PORT_SPEED) \
	ETH_PORT_CHAN=$(ETH_PORT_CHAN) \
	DMA_TYPE=$(DMA_TYPE) \
	DMA_DEBUG_ENABLE=$(DMA_DEBUG_ENABLE) \
	BMC_ENABLE=$(BMC_ENABLE) \
	NET_MOD_ENABLE=$(NET_MOD_ENABLE) \
	APP_CORE_ENABLE=$(APP_CORE_ENABLE) \
	PCIE_CONF=$(PCIE_CONF) \
	USR_CORE_ARCH=$(USR_CORE_ARCH) \
	$(USER_ENV)

include $(OFM_PATH)/build/Makefile.Vivado.inc
