# Vivado.tcl: Vivado tcl script to compile whole FPGA design
# Copyright 2025 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# ----- Setting basic synthesis options ---------------------------------------
# Source configuration files(populates all variables from env)
source $env(CORE_BASE)/config/core_bootstrap.tcl

# Include CORE script
source $CORE_BASE/Vivado.inc.tcl

# Design parameters
set SYNTH_FLAGS(MODULE)    "FPGA"
set SYNTH_FLAGS(FPGA)      "xcv80-lsva4737-2MHP-e-S"
set SYNTH_FLAGS(MCS_IFACE) "SPIx8"
set SYNTH_FLAGS(BOARD)     $CARD_NAME

# Propagating card constants to the Modules.tcl files of the underlying components.
# The description of usage of this array is provided in the Parametrization section
# of the NDK-CORE repository.
set CARD_ARCHGRP(CORE_BASE)             $CORE_BASE
set CARD_ARCHGRP(IP_BUILD_DIR)          $CARD_BASE/src/ip
set CARD_ARCHGRP(IP_GEN_FILES)          false
set CARD_ARCHGRP(PCIE_ENDPOINTS)        $PCIE_ENDPOINTS
set CARD_ARCHGRP(PCIE_ENDPOINT_MODE)    $PCIE_ENDPOINT_MODE
set CARD_ARCHGRP(HBM_PORTS)             $HBM_PORTS

# make lists from associative arrays
set CARD_ARCHGRP_L [array get CARD_ARCHGRP]
set CORE_ARCHGRP_L [array get CORE_ARCHGRP]

# concatenate lists to be handed as a part of the ARCHGRP to the TOPLEVEL
set ARCHGRP_ALL [concat $CARD_ARCHGRP_L $CORE_ARCHGRP_L]

# Main component
lappend HIERARCHY(COMPONENTS) [list "TOPLEVEL" $CARD_BASE/src $ARCHGRP_ALL]

# XDC constraints for specific parts of the design
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/general.xdc"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/pblock.xdc"

lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/pcie_half.xdc"

if {$PCIE_ENDPOINT_MODE == 0 || $PCIE_ENDPOINT_MODE == 1} {
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/pcie_full.xdc"
}

# Create only a Quartus project for further design flow driven from Quartus GUI
# "0" ... full design flow in command line
# "1" ... project composition only for further dedesign flow in GUI
set SYNTH_FLAGS(PROJ_ONLY) "0"

# Associative array which is propagated to APPLICATION_CORE, add other
# parameters if necessary.
set APP_ARCHGRP(APP_CORE_ENABLE) $APP_CORE_ENABLE

# Convert associative array to list
set APP_ARCHGRP_L [array get APP_ARCHGRP]

# ----- Add application core to main component list ---------------------------
lappend HIERARCHY(COMPONENTS) \
    [list "APPLICATION_CORE" "$OFM_PATH/apps/minimal/top" $APP_ARCHGRP_L]

# Call main function which handle targets
nb_main
