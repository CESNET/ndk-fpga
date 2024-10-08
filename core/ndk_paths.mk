# Makefile: Common make script for firmware targets
# Copyright (C) 2024 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

MAKEFILE_BASE := $(dir $(lastword $(MAKEFILE_LIST)))
COMBO_BASE := $(MAKEFILE_BASE)../
OFM_PATH := $(MAKEFILE_BASE)../
# FIRMWARE_BASE variable hack
FIRMWARE_BASE := $(MAKEFILE_BASE)../
