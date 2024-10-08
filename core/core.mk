# core.mk: Common Makefile for all cards
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Supported DMA types (possible values: 0, 3, 4):
# 0 - Disable DMA
# 3 - DMA Medusa
# 4 - DMA Calypte
DMA_TYPE ?= 3
