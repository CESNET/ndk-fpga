# ver_settings.mk: a plain make run of a cocotb bench with the "default" setting of its ver_settings.py
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# A bench includes this file before build/Makefile. Unless GENERICS comes from the command line or the environment,
# as from multi_ver_cocotb.py, the run gets the generics and the COCOTB_* parameters of the "default" setting.
VER_SETTINGS ?= ver_settings.py
VER_SETTINGS_DEFAULT := python3 $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/ver_settings_default.py

ifeq ($(origin GENERICS),undefined)
ifneq ($(wildcard $(VER_SETTINGS)),)
GENERICS := $(shell $(VER_SETTINGS_DEFAULT) --generics $(VER_SETTINGS))
ifneq ($(.SHELLSTATUS),0)
$(error cannot read the "default" setting of $(VER_SETTINGS))
endif
export GENERICS
VER_SETTINGS_COCOTB_ENV := $(shell $(VER_SETTINGS_DEFAULT) --cocotb-env $(VER_SETTINGS))
ifneq ($(.SHELLSTATUS),0)
$(error cannot pass the "__cocotb_params__" of the "default" setting of $(VER_SETTINGS) through make)
endif
$(foreach assignment,$(VER_SETTINGS_COCOTB_ENV),$(eval export $(assignment)))
endif
endif
