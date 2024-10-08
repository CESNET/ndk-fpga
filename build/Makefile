# Makefile: Common make script for firmware targets
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SYNTH ?= vivado

MAKEFILE_BASE ?= $(dir $(lastword $(MAKEFILE_LIST)))
FIRMWARE_BASE ?= $(MAKEFILE_BASE)../
OFM_PATH ?= $(MAKEFILE_BASE)../

# Override target; needs to be supported in original target
# This is useful when the user needs to use target-specific variables with other target
TARGET ?=

# Select main Makefile with SYNTH tool variable
ifeq ($(SYNTH),vivado)
	SYNTH_MAKEFILE := build/Makefile.Vivado.inc
else ifeq ($(findstring quartus,$(SYNTH)),quartus)
	SYNTH_MAKEFILE := build/Makefile.Quartus.inc
else ifeq ($(findstring synplify,$(SYNTH)),synplify)
	SYNTH_MAKEFILE := build/Makefile.Synplify.inc
else
	$(error "Unknown synth tool '$(SYNTH)', please update common Makefile")
endif

include $(OFM_PATH)$(SYNTH_MAKEFILE)

# For lazy users
.PHONY: vivado quartus synplify
vivado quartus synplify:
	@$(MAKE) SYNTH=$@
