# Makefile: Common make script for firmware targets
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Some basic tools
RM ?= rm -f
TCLSH ?= tclsh

.PHONY: simulation vhdocl cocotb

GEN_MK_TARGETS += simulation vhdocl cocotb ghdl-sim nvc-sim
simulation: GEN_MK_ENV=SIM_SCRIPT=$(SIM_SCRIPT) SIM_FLAGS=$(SIM_FLAGS)

MAKE_REC = $(MAKE) -f $(firstword $(MAKEFILE_LIST)) --no-print-directory $(NETCOPE_ENV)

define print_label
	@echo '*****************************************************************************'
	@echo '* $(1)'
	@echo '*****************************************************************************'
endef

GEN_MK_NAME ?= $(OUTPUT_NAME).$(SYNTH).mk

# The generated .mk file $(GEN_MK_NAME) contains the $(MOD) variable
# (a list of all source filenames) and some dynamically TCL generated targets.
#
# All targets, which depends on $(MOD) variable, must be called in two phases:
# 1. Main run of make:
# 		- target depends on $(GEN_MK_NAME) only (this will generate the file)
# 		- target executes recursion of make
# 2. Recursive run of make:
# 		- already generated file $(GEN_MK_NAME) is included
# 		- $(MOD) variable can be used to determine dependencies
#		- real target is executed
#
# Rule for $(GEN_MK_NAME) is better than previous approach (in which the file
# was generated always, in the parse phase of the main Makefile):
# - it reflects target-specific assignments
# - output of the process of generation $(GEN_MK_NAME) can be printed to user
# - allows user to include this Makefile system even some Modules.tcl not yet exists

# a) In the recursive run of make include the generated file $(GEN_MK_NAME)
# 	- all real rules must be specified in main Makefile and wrapped in similar condition
# b) In the main run of make create a rule for the $(GEN_MK_NAME) and rule for all targets, which needs $(GEN_MK_NAME)
#   - user must specify all those targets in the $(GEN_MK_TARGETS) variable within main Makefile
ifneq ($(GEN_MK_TARGET),)
include $(GEN_MK_NAME)

simulation: $(MOD)
	$(NETCOPE_ENV) vsim -64 -do "$(SIM_SCRIPT)" $(SIM_FLAGS)

.PHONY: cocotb
COCOTB_SIM_SCRIPT ?= $(OFM_PATH)/build/scripts/cocotb/cocotb.fdo
COCOTB_MODULE ?= cocotb_test
cocotb: $(MOD)
	$(NETCOPE_ENV) SYNTHFILES=$(SYNTHFILES) COCOTB_MODULE=$(COCOTB_MODULE) vsim -64 -do $(COCOTB_SIM_SCRIPT) $(SIM_FLAGS)

# Automated documentation script
vhdocl:
	echo "outputdir=vhdocl.doc" > vhdocl.conf
	for m in $(MOD); do echo $$m | grep .vhd | sed 's/^/input\ /' >> vhdocl.conf; done
	vhdocl -f vhdocl.conf

GHDL_WORK_DIR?=work_ghdl
ghdl-sim: $(MOD)
	@mkdir -p $(GHDL_WORK_DIR)
	$(eval TOP_LEVEL_ENT_LC:=$(shell echo $(TOP_LEVEL_ENT) | tr '[:upper:]' '[:lower:]'))
	ghdl -i --workdir=$(GHDL_WORK_DIR) $(addprefix -P,$(GHDL_LIBS)) --std=08 -frelaxed --ieee=synopsys $(filter %.vhd,$(MOD))
	ghdl -m --workdir=$(GHDL_WORK_DIR) $(addprefix -P,$(GHDL_LIBS)) --std=08 -frelaxed --ieee=synopsys --warn-no-hide $(TOP_LEVEL_ENT_LC)
	MODULE=$(COCOTB_MODULE) TOPLEVEL=$(TOP_LEVEL_ENT_LC) TOPLEVEL_LANG=vhdl $(NETCOPE_ENV) COCOTB_RESOLVE_X=ZEROS \
	ghdl -r -v --workdir=$(GHDL_WORK_DIR) -P$(GHDL_WORK_DIR) $(addprefix -P,$(GHDL_LIBS)) $(TOP_LEVEL_ENT_LC) --vpi=$(shell cocotb-config --lib-name-path vpi ghdl) --asserts=disable --vcd=$(OUTPUT_NAME).vcd

nvc-sim: $(MOD)
	$(eval TOP_LEVEL_ENT_LC:=$(shell echo $(TOP_LEVEL_ENT) | tr '[:upper:]' '[:lower:]'))
	nvc --std=2008 -a --relaxed $(filter %.vhd,$(MOD))
	nvc -M 4G -e  $(TOP_LEVEL_ENT_LC)
	MODULE=$(COCOTB_MODULE) TOPLEVEL=$(TOP_LEVEL_ENT_LC) TOPLEVEL_LANG=vhdl $(NETCOPE_ENV) COCOTB_RESOLVE_X=ZEROS \
	nvc -M 4G -r $(TOP_LEVEL_ENT_LC) --ieee-warnings=off --load $(shell cocotb-config --lib-name-path vhpi nvc)

else
.PHONY: $(GEN_MK_NAME)
$(GEN_MK_NAME):
	$(call print_label,Generate Makefile "$(GEN_MK_NAME)" with prerequisites)
	@$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t makefile -p $(GEN_MK_NAME)

$(GEN_MK_TARGETS): $(GEN_MK_NAME)
	@$(MAKE_REC) $(GEN_MK_ENV) GEN_MK_TARGET=1 $@
endif
