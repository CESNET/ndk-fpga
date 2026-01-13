# Vivado.tcl: Vivado tcl script to compile whole FPGA design
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

set OUTPUT_NAME   $env(OUTPUT_NAME)
set OFM_PATH      $env(OFM_PATH)
set COMBO_BASE    $env(COMBO_BASE)
set FIRMWARE_BASE $env(FIRMWARE_BASE)
set CARD_BASE     $env(CARD_BASE)
set CORE_BASE     $env(CORE_BASE)

set CORE_FUNC  $COMBO_BASE/core/config/core_func.tcl
set APP_CONF $env(APP_CONF)

source $OFM_PATH/build/VhdlPkgGen.tcl
source $OFM_PATH/build/Vivado.inc.tcl
source $COMBO_BASE/core/ip/common.tcl

VhdlPkgBegin

# Source CORE functions
source $CORE_FUNC
# Source configuratble parameters
source $APP_CONF

set SYNTH_FLAGS(OUTPUT) $OUTPUT_NAME

# Prerequisites for generated VHDL package
set UCP_PREREQ [list $APP_CONF]

# Let generate package from configuration files and add it to project
lappend HIERARCHY(PACKAGES) [nb_generate_file_register_userpkg "combo_user_const" "" $UCP_PREREQ]

# Let generate DevTree.vhd and add it to project
lappend HIERARCHY(PACKAGES) [nb_generate_file_register_devtree]

# ----- Default target: synthesis of the project ------------------------------
proc target_default {} {
    global SYNTH_FLAGS HIERARCHY
    SynthesizeProject SYNTH_FLAGS HIERARCHY
}

# ----- Setting basic synthesis options ---------------------------------------
set SYNTH_FLAGS(MODULE)    "CARD_TOP"
set SYNTH_FLAGS(FPGA)      "xcu55c-fsvh2892-2L-e"
set SYNTH_FLAGS(MCS_IFACE) "SPIx4"
set SYNTH_FLAGS(BOARD)     $CARD_NAME

# Create only a Vivado project for further design GUI flow
# "0" ... full design flow in command line
# "1" ... gather sources and create project 
set SYNTH_FLAGS(PROJ_ONLY) "1"

# Synthesize the created project (does not take effect if PROJ_ONLY is "1") 
# "0" ... full design flow in command line
# "1" ... synthesize the project
set SYNTH_FLAGS(SYNTH_ONLY) "0"

# Associative array which is propagated throughout Modules.tcl files
set APP_ARCHGRP(CORE_BASE)       $CORE_BASE
set APP_ARCHGRP(CLOCK_GEN_ARCH)  $CLOCK_GEN_ARCH
set APP_ARCHGRP(PCIE_MOD_ARCH)   $PCIE_MOD_ARCH
set APP_ARCHGRP(SDM_SYSMON_ARCH) $SDM_SYSMON_ARCH

set APP_ARCHGRP(PCIE_GEN)           $PCIE_GEN 
set APP_ARCHGRP(PCIE_ENDPOINTS)     $PCIE_ENDPOINTS 
set APP_ARCHGRP(PCIE_ENDPOINT_MODE) $PCIE_ENDPOINT_MODE

set APP_ARCHGRP(IP_BUILD_DIR)     $CARD_BASE/src
set APP_ARCHGRP(IP_GEN_FILES)     false 
set APP_ARCHGRP(IP_MODIFY_BASE)   $COMBO_BASE/cards/amd/alveo-u55c/src/ip
set APP_ARCHGRP(USE_IP_SUBDIRS)   true 
set APP_ARCHGRP(USR_CORE_ARCH)    $USR_CORE_ARCH

# Convert associative array to list
set APP_ARCHGRP_L [array get APP_ARCHGRP]

# --------- Add source files for the design ---------------------------------------
lappend HIERARCHY(COMPONENTS) [list "CORE_LOGIC" "$OFM_PATH/apps/sparklev/comp" $APP_ARCHGRP_L]

lappend HIERARCHY(MOD) "$CARD_BASE/src/card_top.vhd"

# --------- Add constraints to the design ---------------------------------------
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/src/general.xdc"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/src/pblock.xdc"

lappend SYNTH_FLAGS(CONSTR) "$COMBO_BASE/cards/amd/alveo-u55c/constr/pcie_x4.xdc"

if {$PCIE_ENDPOINT_MODE == 0 || $PCIE_ENDPOINT_MODE == 1 || $PCIE_ENDPOINT_MODE == 2} {
    lappend SYNTH_FLAGS(CONSTR) "$COMBO_BASE/cards/amd/alveo-u55c/constr/pcie_x8.xdc"
}

if {$PCIE_ENDPOINT_MODE == 0 || $PCIE_ENDPOINT_MODE == 1} {
    lappend SYNTH_FLAGS(CONSTR) "$COMBO_BASE/cards/amd/alveo-u55c/constr/pcie_x16.xdc"
}

# Call main function which handle targets
nb_main
