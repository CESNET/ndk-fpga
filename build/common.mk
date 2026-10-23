# Makefile: Common make script for firmware targets
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Some basic tools
RM ?= rm -f
TCLSH ?= tclsh

.PHONY: simulation vhdocl cocotb clean_common

GEN_MK_TARGETS += simulation vhdocl cocotb ghdl-sim nvc nvc-sim nvc-elab nvc-run
simulation: GEN_MK_ENV=SIM_SCRIPT=$(SIM_SCRIPT) SIM_FLAGS=$(SIM_FLAGS)

NVC_PLATFORM_TAGS ?= altera xilinx
nvc nvc-sim nvc-elab nvc-run: NETCOPE_ENV+=PLATFORM_TAGS="$(NVC_PLATFORM_TAGS)"

# INFO: NETCOPE_TEMP is generated directory
clean_common:
	-@$(RM) -r nvcwork/ $(NETCOPE_TEMP)
	-@$(RM) DevTree_paths.txt vhdocl.doc vhdocl.conf

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
COCOTB_TEST_MODULES ?= $(COCOTB_MODULE)
cocotb: $(MOD)
	$(NETCOPE_ENV) SYNTHFILES=$(SYNTHFILES) COCOTB_TEST_MODULES=$(COCOTB_TEST_MODULES) vsim -64 -do $(COCOTB_SIM_SCRIPT) $(SIM_FLAGS)

# Automated documentation script
vhdocl:
	echo "outputdir=vhdocl.doc" > vhdocl.conf
	for m in $(MOD); do echo $$m | grep .vhd | sed 's/^/input\ /' >> vhdocl.conf; done
	vhdocl -f vhdocl.conf

COCOTB_GPI_USERS_ENV = $(shell cocotb-config --pygpi-entry-point >/dev/null 2>&1 && printf 'GPI_USERS="%s;%s"' "$$(cocotb-config --libpython)" "$$(cocotb-config --pygpi-entry-point)")

# NVC_LOAD marks a cocotb run. Its results.xml is removed before the run and must exist afterwards without a
# failure, as --exit-severity fails a run only on a VHDL or PSL abort, not on a failed test or an unimportable module.
define clear_cocotb_results
	@if [ -n "$(NVC_LOAD)" ]; then rm -f results.xml; fi
endef

define check_cocotb_results
	@if [ -n "$(NVC_LOAD)" ]; then \
		if [ ! -f results.xml ]; then \
			echo "*** cocotb wrote no results.xml -- see the log above ***" >&2; \
			exit 1; \
		fi; \
		if grep -q '<failure' results.xml; then \
			echo "*** cocotb reported a test FAILURE -- see results.xml ***" >&2; \
			exit 1; \
		fi; \
	fi
endef

COCOTB_RUN_ARGS:=

ifneq ($(RANDOM_SEED),)
COCOTB_RUN_ARGS += COCOTB_RANDOM_SEED=$(RANDOM_SEED)
endif

# The assignments before $(NETCOPE_ENV) are defaults that USER_ENV, a part of it, can override.
COCOTB_ENV=\
MODULE=$(COCOTB_TEST_MODULES) \
COCOTB_TEST_MODULES=$(COCOTB_TEST_MODULES) \
PYGPI_PYTHON_BIN=$(shell cocotb-config --python-bin) \
$(COCOTB_GPI_USERS_ENV) \
TOPLEVEL=$(TOP_LEVEL_ENT_LC) \
TOPLEVEL_LANG=vhdl \
$(NETCOPE_ENV) \
$(COCOTB_RUN_ARGS) \
COCOTB_RESOLVE_X=ZEROS

GHDL_WORK_DIR?=work_ghdl
ghdl-sim: $(MOD)
	@mkdir -p $(GHDL_WORK_DIR)
	$(eval TOP_LEVEL_ENT_LC:=$(shell echo $(TOP_LEVEL_ENT) | tr '[:upper:]' '[:lower:]'))
	ghdl -i --workdir=$(GHDL_WORK_DIR) $(addprefix -P,$(GHDL_LIBS)) --std=08 -frelaxed --ieee=synopsys $(filter %.vhd,$(MOD))
	ghdl -m --workdir=$(GHDL_WORK_DIR) $(addprefix -P,$(GHDL_LIBS)) --std=08 -frelaxed --ieee=synopsys --warn-no-hide $(TOP_LEVEL_ENT_LC)
	$(COCOTB_ENV) ghdl -r -v --workdir=$(GHDL_WORK_DIR) -P$(GHDL_WORK_DIR) $(addprefix -P,$(GHDL_LIBS)) $(TOP_LEVEL_ENT_LC) --vpi=$(shell cocotb-config --lib-name-path vpi ghdl) --asserts=disable --vcd=$(OUTPUT_NAME).vcd

# PSL is opt-in (NVC_PSL=1) because the PSL directives in the tree are not all accepted by nvc yet.
NVC_PSL ?=
NVC_ANALYSE_FLAGS ?= --relaxed
# Kept out of NVC_ANALYSE_FLAGS, so that one given on the make command line does not drop --psl.
NVC_PSL_FLAGS :=
ifeq ($(NVC_PSL),1)
NVC_PSL_FLAGS += --psl
endif

# With an empty NVC_EXIT_SEVERITY, nvc keeps running after a PSL or VHDL error and cocotb still
# reports PASS. Setting it, e.g. to "error", aborts the run so that cocotb marks it as failed too.
NVC_EXIT_SEVERITY ?=
# Kept out of NVC_RUN_ARGS, so that one given on the make command line does not drop --exit-severity.
NVC_EXIT_SEVERITY_FLAGS :=
ifneq ($(NVC_EXIT_SEVERITY),)
NVC_EXIT_SEVERITY_FLAGS += --exit-severity=$(NVC_EXIT_SEVERITY)
endif

NVC_LOAD ?=
# Wave dumping (FST + gtkw + arrays); enable with WAVES=1.
NVC_WAVE_FLAGS ?=
ifeq ($(WAVES),1)
NVC_WAVE_FLAGS := -w --dump-arrays -g
# Keep hierarchical signals visible in gtkwave (also better for some small
# cocotb-heavy designs, but ~4x slower on large toplevel sims).
NVC_NO_COLLAPSE ?= 1
endif
# Default: allow signal collapse + -O3 (much faster on large designs).
# Set NVC_NO_COLLAPSE=1 for wave debug or if a small TB regresses.
NVC_ELAB_FLAGS ?= -O3
ifeq ($(NVC_NO_COLLAPSE),1)
NVC_ELAB_FLAGS += --no-collapse
endif
nvc-sim: NVC_LOAD=--load $(shell cocotb-config --lib-name-path vhpi nvc)
nvc-sim: nvc
nvc-run: NVC_LOAD=--load $(shell cocotb-config --lib-name-path vhpi nvc)

# Extra environment variables for the nvc -r step only, e.g. LD_LIBRARY_PATH for a project, without
# affecting the tclsh mk-file generation that also uses NETCOPE_ENV.
NVC_RUN_ENV ?=

TOP_LEVEL_ENT_LC := $(shell echo $(TOP_LEVEL_ENT) | tr '[:upper:]' '[:lower:]')

# Analysis and elaboration of the nvc flow, shared by nvc and nvc-elab.
define nvc_analyse_elab
	@nvc --work=nvcwork -H 1G -M 4G --std=2008 -a $(NVC_ANALYSE_FLAGS) $(NVC_PSL_FLAGS) $(filter %.vhd,$(MOD))
	@nvc --work=nvcwork -H 1G -M 4G -e $(NVC_ELAB_FLAGS) $(NVC_ELAB_ARGS) $(TOP_LEVEL_ENT_LC)
endef

# The cocotb run of the nvc flow, shared by nvc and nvc-run.
define nvc_run
	$(call clear_cocotb_results)
	@$(NVC_RUN_ENV) $(COCOTB_ENV) nvc --work=nvcwork -H 1G -M 4G -r $(NVC_EXIT_SEVERITY_FLAGS) $(NVC_RUN_ARGS) $(TOP_LEVEL_ENT_LC) $(NVC_WAVE_FLAGS) --ieee-warnings=off $(NVC_LOAD)
	$(call check_cocotb_results)
endef

nvc: $(MOD)
	$(call nvc_analyse_elab)
	$(call nvc_run)

# Analyse and elaborate only, so that nvcwork/ is built once and reused by repeated nvc-run calls.
nvc-elab: $(MOD)
	$(call nvc_analyse_elab)

# Run on the nvcwork/ left by nvc-elab, skipping analysis and elaboration; the cocotb Python is
# loaded at run time, so editing it needs no rebuild.
nvc-run: $(MOD)
	$(call nvc_run)

else
.PHONY: $(GEN_MK_NAME)
$(GEN_MK_NAME):
	$(call print_label,Generate Makefile "$(GEN_MK_NAME)" with prerequisites)
	@$(NETCOPE_ENV) $(TCLSH) $(SYNTHFILES) -t makefile -p $(GEN_MK_NAME)

$(GEN_MK_TARGETS): $(GEN_MK_NAME)
	@$(MAKE_REC) $(GEN_MK_ENV) GEN_MK_TARGET=1 $@
endif
