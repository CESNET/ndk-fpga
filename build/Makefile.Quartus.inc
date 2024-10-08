# Makefile.Quartus.inc: Include Makefile for compilation with Quartus
# Copyright (C) 2017 CESNET
# Author: Jiri Matousek <matousek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

ifeq ($(SYNTH),quartus)
override SYNTH=quartus_sh
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
DEVICE?=STRATIX10

# This is our main tool
SYNTH ?= quartus_sh
SYNTHFLAGS ?= -t
SYNTHFILES ?= Quartus.tcl
USER_ENV ?=
NETCOPE_ENV ?= \
	OFM_PATH=$(OFM_PATH)\
	FIRMWARE_BASE=$(FIRMWARE_BASE)\
	OUTPUT_NAME=$(OUTPUT_NAME)\
	TOP_LEVEL_ENT=$(TOP_LEVEL_ENT)\
	TOP_LEVEL_ARCHGRP=$(TOP_LEVEL_ARCHGRP)\
	TOP_LEVEL_PATH=$(TOP_LEVEL_PATH)\
	$(USER_ENV)

NETCOPE_ENV+=NETCOPE_TEMP=$(NETCOPE_TEMP) SYNTH_TOOL=quartus

GEN_MK_TARGETS = $(TOP_LEVEL_ENT).vho $(OUTPUT_NAME).sof
include $(dir $(lastword $(MAKEFILE_LIST)))common.mk

# Additional targets for make clean
CLEAN_DEPENDS ?=

# Additional targets for make cleanall
CLEANALL_DEPENDS ?=

.PRECIOUS: %.vho %.sof %DevTree.vhd

.PHONY: comp clean_build clean cleanall

ttarget_%:
	$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t $*
starget_%:
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES) -t $*

# Main target for synthesize components
comp: export CLK_PORTS:=$(CLK_PORTS)
comp: export CLK_PERIOD:=$(CLK_PERIOD)
comp: export DEVICE:=$(DEVICE)
comp: export SYNTHFILES:=$(OFM_PATH)/build/targets/comp_quartus.tcl
ifneq ($(TARGET),)
comp: $(TARGET)
else
comp: $(TOP_LEVEL_ENT).vho
endif

# Main target for building design - for non-constant OUTPUT_NAME (variable is assigned in target) must be executed recursively
build:
	@if [ -z "$(TARGET)" ] ; then $(MAKE_REC) $(OUTPUT_NAME).sof; else $(MAKE_REC) $(TARGET); fi

# These targets will be only available at second recursive run, because they needed variables from generated Makefile $(MOD)
ifneq ($(GEN_MK_TARGET),)

$(TOP_LEVEL_ENT).vho: $(MOD) $(SYNTHFILES)
	$(call print_label,Synthesize $@ (VHDL -> VHO))
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES)

$(OUTPUT_NAME).sof: $(MOD) $(SYNTHFILES)
	$(call print_label,Implement $@ (VHDL -> SOF))
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES)

endif

# Built-in cleanup
clean_build:
	-@$(RM) *.vho *.sof *.prj \
                *.qpf *.qsf *.qws *.pin *.sld \
                *.rpt *.summary *.done
	-@$(RM) -r qdb tmp-clearbox
	-@$(RM) -r DevTree_paths.txt
	-@$(RM) -r $(NETCOPE_TEMP) $(OUTPUT_NAME).quartus.mk $(OUTPUT_NAME).quartus_sh.mk

# User's chance to add own cleaning stuff
clean: clean_build $(CLEAN_DEPENDS)

# User's chance to add own 'hard' cleaning stuff (e.g. removing module checkpoints)
cleanall: clean $(CLEANALL_DEPENDS)
