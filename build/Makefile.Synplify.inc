# Makefile.Synplify.inc: Include Makefile for compilation with Synplify
# Copyright (C) 2023 BrnoLogic
# Author: Lukas Kekely <kekely@brnologic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

ifeq ($(SYNTH),synplify)
override SYNTH=synplify_pro
endif

ifneq ($(TOP_LEVEL_ENT),)
OUTPUT_NAME?=$(TOP_LEVEL_ENT)
endif

NETCOPE_TEMP?=$(OUTPUT_NAME).netcope_tmp/

# Main target for synthesize components
TOP_LEVEL_ARCHGRP?=FULL
TOP_LEVEL_PATH?=..
CLK_PORTS?=CLK
CLK_PERIOD?=5.0

# This is our main tool
SYNTH ?= synplify_pro
SYNTHFLAGS ?= -batch -tcl
SYNTHFILES ?= Synplify.tcl
USER_ENV ?=
NETCOPE_ENV ?= \
	OFM_PATH=$(OFM_PATH)\
	FIRMWARE_BASE=$(FIRMWARE_BASE)\
	OUTPUT_NAME=$(OUTPUT_NAME)\
	TOP_LEVEL_ENT=$(TOP_LEVEL_ENT)\
	TOP_LEVEL_ARCHGRP=$(TOP_LEVEL_ARCHGRP)\
	TOP_LEVEL_PATH=$(TOP_LEVEL_PATH)\
	$(USER_ENV)

NETCOPE_ENV+=NETCOPE_TEMP=$(NETCOPE_TEMP) SYNTH_TOOL=synplify

GEN_MK_TARGETS = $(TOP_LEVEL_ENT).edf
include $(dir $(lastword $(MAKEFILE_LIST)))common.mk

# Additional targets for make clean
CLEAN_DEPENDS ?=

# Additional targets for make cleanall
CLEANALL_DEPENDS ?=

.PRECIOUS: %.edf %DevTree.vhd

.PHONY: comp clean_build clean cleanall

ttarget_%:
	$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t $*
starget_%:
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES) -t $*

# Main target for synthesize components
comp: export CLK_PORTS:=$(CLK_PORTS)
comp: export CLK_PERIOD:=$(CLK_PERIOD)
comp: export DEVICE:=$(DEVICE)
comp: export SYNTHFILES:=$(OFM_PATH)/build/targets/comp_synplify.tcl
ifneq ($(TARGET),)
comp: $(TARGET)
else
comp: $(TOP_LEVEL_ENT).edf
endif

# Main target for building design - for non-constant OUTPUT_NAME (variable is assigned in target) must be executed recursively
build:
	$(MAKE_REC) $(TARGET)

# These targets will be only available at second recursive run, because they needed variables from generated Makefile $(MOD)
ifneq ($(GEN_MK_TARGET),)

$(TOP_LEVEL_ENT).edf: $(MOD) $(SYNTHFILES)
	$(call print_label,Synthesize $@ (VHDL -> EDF))
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES)

endif

# Built-in cleanup
clean_build:
	-@$(RM) *.edf *.prj stdout.log* synlog.tcl
	-@$(RM) -r synth1 rev_1
	-@$(RM) -r DevTree_paths.txt
	-@$(RM) -r $(NETCOPE_TEMP) $(OUTPUT_NAME).synplify_pro.mk

# User's chance to add own cleaning stuff
clean: clean_build $(CLEAN_DEPENDS)

# User's chance to add own 'hard' cleaning stuff (e.g. removing module checkpoints)
cleanall: clean $(CLEANALL_DEPENDS)
