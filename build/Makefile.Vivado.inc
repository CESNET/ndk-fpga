# Makefile.Vivado.inc: Include Makefile for compilation with Vivado
# Copyright (C) 2013 CESNET
# Author: Viktor Pus <pus@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

ifneq ($(TOP_LEVEL_ENT),)
OUTPUT_NAME?=$(TOP_LEVEL_ENT)
endif

NETCOPE_TEMP?=$(OUTPUT_NAME).netcope_tmp/

# Main target for synthesize components
TOP_LEVEL_ARCHGRP?=FULL
TOP_LEVEL_PATH?=..
CLK_PORTS?=CLK
CLK_PERIOD?=5.0
DEVICE?=ULTRASCALE

# This is our main tool
SYNTH ?= vivado
SYNTHFLAGS ?= -notrace -nojournal -log $(OUTPUT_NAME).log -mode batch -source
SYNTHFILES ?= Vivado.tcl
USER_ENV ?=
NETCOPE_ENV ?= \
	OFM_PATH=$(OFM_PATH)\
	FIRMWARE_BASE=$(FIRMWARE_BASE)\
	OUTPUT_NAME=$(OUTPUT_NAME)\
	TOP_LEVEL_ENT=$(TOP_LEVEL_ENT)\
	TOP_LEVEL_ARCHGRP=$(TOP_LEVEL_ARCHGRP)\
	TOP_LEVEL_PATH=$(TOP_LEVEL_PATH)\
	$(USER_ENV)

NETCOPE_ENV+=NETCOPE_TEMP=$(NETCOPE_TEMP) SYNTH_TOOL=vivado

GEN_MK_TARGETS = $(TOP_LEVEL_ENT).edf $(MODULE).dcp $(OUTPUT_NAME).nfw
include $(dir $(lastword $(MAKEFILE_LIST)))common.mk

# Additional targets for make clean
CLEAN_DEPENDS ?=

# Additional targets for make cleanall
CLEANALL_DEPENDS ?=

.PRECIOUS: %.edf %.bit %.nfw %DevTree.vhd

.PHONY: comp build clean_build clean cleanall warn warn_synth

ttarget_%:
	$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t $*
starget_%:
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES) -t $*

# Main target for synthesize components
comp: export CLK_PORTS:=$(CLK_PORTS)
comp: export CLK_PERIOD:=$(CLK_PERIOD)
comp: export DEVICE:=$(DEVICE)
comp: export SYNTHFILES:=$(OFM_PATH)/build/targets/comp_vivado.tcl
ifneq ($(TARGET),)
comp: $(TARGET)
else
comp: $(TOP_LEVEL_ENT).edf
endif

# Main target for building design - for non-constant OUTPUT_NAME (variable is assigned in target) must be executed recursively
build:
	@if [ -z "$(TARGET)" ] ; then $(MAKE_REC) $(OUTPUT_NAME).nfw; else $(MAKE_REC) $(TARGET); fi

# These targets will be only available at second recursive run, because they needed variables from generated Makefile $(MOD)
ifneq ($(GEN_MK_TARGET),)

$(TOP_LEVEL_ENT).edf: $(MOD) $(SYNTHFILES)
	$(call print_label,Synthesize $@ (VHDL -> EDIF))
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES)

$(MODULE).dcp: $(MOD) $(SYNTHFILES)
	$(call print_label,Synthesize $@ (VHDL -> DCP))
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES)

$(OUTPUT_NAME).nfw: $(MOD) $(SYNTHFILES)
	$(call print_label,Implement $@ (VHDL -> NFW))
	$(NETCOPE_ENV) $(SYNTH) $(SYNTHFLAGS) $(SYNTHFILES)

endif

# Built-in cleanup
clean_build:
	-@$(RM) *.edf *.bit *.mcs *.nfw *.edn \
		*_synth.tim *_synth.util *.jou *.xpr *.log *_par.tim *_par.util *_par.pow *.prj \
                messages-* *_synth.drc *_par.drc
	-@$(RM) -r *.dcp *.prm
	-@$(RM) -r *.data *.runs *.cache *.filter *.hw *.sim .Xil *.ip_user_files
	-@$(RM) -r vhdocl.doc vhdocl.conf
	-@$(RM) -r DevTree_paths.txt
	-@$(RM) -r $(NETCOPE_TEMP) $(OUTPUT_NAME).vivado.mk

# User's chance to add own cleaning stuff
clean: clean_build $(CLEAN_DEPENDS)

# Clean really everything (e.g. module checkpoints)
cleanall: clean $(CLEANALL_DEPENDS)

# Warning checks will be added
warn: warn_synth
	@echo "Constraint compliance:"
	@echo "This is TODO, sorry..."

warn_synth:
	@echo "Extremely suspicious warnings by Vivado:"
	@echo "This is TODO, sorry..."
