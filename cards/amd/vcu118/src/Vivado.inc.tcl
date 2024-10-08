# Vivado.inc.tcl: Vivado.tcl include
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source configuration files(populates all variables from env)
source $env(CORE_BASE)/config/core_bootstrap.tcl

# Include CORE script
source $CORE_BASE/Vivado.inc.tcl

# Design parameters
set SYNTH_FLAGS(MODULE)    "FPGA"
set SYNTH_FLAGS(FPGA)      "xcvu9p-flga2104-2L-e"
set SYNTH_FLAGS(MCS_IFACE) "SPIx8"
set SYNTH_FLAGS(BOARD)     $CARD_NAME

# Optimization directives for implementation
set SYNTH_FLAGS(SOPT_DIRECTIVE)  "Explore"
set SYNTH_FLAGS(PLACE_DIRECTIVE) "Explore"
set SYNTH_FLAGS(POPT_DIRECTIVE)  "Explore"
set SYNTH_FLAGS(ROUTE_DIRECTIVE) "Explore"

# Propagating card constants to the Modules.tcl files of the underlying components.
# The description of usage of this array is provided in the Parametrization section
# of the NDK-CORE repository documentation.
set CARD_ARCHGRP(CORE_BASE) $CORE_BASE
set CARD_ARCHGRP(PCIE_ENDPOINT_MODE) $PCIE_ENDPOINT_MODE

# make lists from associative arrays
set CARD_ARCHGRP_L [array get CARD_ARCHGRP]
set CORE_ARCHGRP_L [array get CORE_ARCHGRP]

# concatenate lists to be handed as a part of the ARCHGRP to the TOPLEVEL
set ARCHGRP_ALL [concat $CARD_ARCHGRP_L $CORE_ARCHGRP_L]

# Main component
lappend HIERARCHY(COMPONENTS) [list "TOPLEVEL" $CARD_BASE/src $ARCHGRP_ALL]

lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/general.xdc"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/pcie.xdc"

if {$NET_MOD_ARCH != "EMPTY"} {
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/qsfp.xdc"
    lappend SYNTH_FLAGS(CONSTR) [list "$CARD_BASE/constr/gty_loc.xdc" USED_IN implementation]
} else {
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/qsfp_disconnect.xdc"
}

# lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/ddr4.xdc"
