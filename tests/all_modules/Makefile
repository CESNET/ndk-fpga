# Makefile: vhdl_ls.toml generator
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

TOP_LEVEL_ENT=ALL_ENTITIES

OFM_PATH=../../
TOP_LEVEL_PATH=.
TEMP_MOD_TCL=Modules.tcl

EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/pcie/common/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/*/dsp_counter_intel/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/*/dsp_comparator_intel/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/fl_tools/flow/switch/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/nic/mac_lite/rx_mac_lite/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/nic/mac_lite/tx_mac_lite/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/nic/ver/Modules.tcl'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/fl_tools/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/mi_tools/sim_old/*'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/*/sim/*Modules.tcl'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/*/ver/*Modules.tcl'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/*/ver_*/*Modules.tcl'
EXCLUDE_COMP += -not -path '$(OFM_PATH)/comp/*/uvm/*Modules.tcl'

EXCLUDE_GLOB += -not -path '*/comp/*/ver/*Modules.tcl'

.PHONY: all
all: vhdl_ls_toml

vhdl_ls_toml:
	@echo -n > $(TEMP_MOD_TCL)
	@find $(OFM_PATH)/comp/       $(EXCLUDE_COMP) -name Modules.tcl >> $(TEMP_MOD_TCL) || true
	@find $(OFM_PATH)/extra/dma-* $(EXCLUDE_GLOB) -name Modules.tcl >> $(TEMP_MOD_TCL) || true
	@find $(OFM_PATH)/extra/ndk-* $(EXCLUDE_GLOB) -name Modules.tcl >> $(TEMP_MOD_TCL) || true
	@sed 's=\(.*\)Modules.tcl=lappend COMPONENTS [list "X" $$ENTITY_BASE/\1 "FULL"]=' -i $(TEMP_MOD_TCL)
	@touch DevTree_paths.txt
	@$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t generate_file -p $(shell pwd -P)/$(TOP_LEVEL_ENT).netcope_tmp/DevTree.vhd
	@$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t generate_file -p $(shell pwd -P)/$(TOP_LEVEL_ENT).netcope_tmp/netcope_const.vhd
	@$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t generate_file -p $(shell pwd -P)/$(TOP_LEVEL_ENT).netcope_tmp/ndk_fpga_common_pkg.vhd
	@$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t generate_file -p $(shell pwd -P)/$(TOP_LEVEL_ENT).netcope_tmp/ndk_app_pkg.vhd
	@$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t generate_file -p $(shell pwd -P)/$(TOP_LEVEL_ENT).netcope_tmp/ndk_fpga_top_pkg.vhd
	@make SYNTHFILES=Vivado.tcl TARGET=ttarget_vhdl_ls_toml comp

include $(OFM_PATH)/build/Makefile
