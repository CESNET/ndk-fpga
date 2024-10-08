# Vivado.inc.tcl: Vivado.tcl include
# Copyright (C) 2022 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source configuration files(populates all variables from env)
source $env(CORE_BASE)/config/core_bootstrap.tcl

# Include CORE script
source $CORE_BASE/Vivado.inc.tcl

# Design parameters
set SYNTH_FLAGS(MODULE)    "fpga"
set SYNTH_FLAGS(FPGA)      "xcvu9p-flgb2104-2-i"
set SYNTH_FLAGS(MCS_IFACE) "SMAPx32"
set SYNTH_FLAGS(BOARD)     $CARD_NAME

# Optimization directives for implementation
set SYNTH_FLAGS(SOPT_DIRECTIVE)  "Explore"
set SYNTH_FLAGS(PLACE_DIRECTIVE) "Explore"
set SYNTH_FLAGS(POPT_DIRECTIVE)  "Explore"
set SYNTH_FLAGS(ROUTE_DIRECTIVE) "Explore"

# Propagating card constants to the Modules.tcl files of the underlying components.
# The description of usage of this array is provided in the Parametrization section
# of the NDK-CORE repository documentation.
set CARD_ARCHGRP(CORE_BASE)          $CORE_BASE
set CARD_ARCHGRP(IP_BUILD_DIR)       $CARD_BASE/src/ip
set CARD_ARCHGRP(IP_GEN_FILES)       false
set CARD_ARCHGRP(PCIE_ENDPOINT_MODE) $PCIE_ENDPOINT_MODE

# make lists from associative arrays
set CARD_ARCHGRP_L [array get CARD_ARCHGRP]
set CORE_ARCHGRP_L [array get CORE_ARCHGRP]

# concatenate lists to be handed as a part of the ARCHGRP to the TOPLEVEL
set ARCHGRP_ALL [concat $CARD_ARCHGRP_L $CORE_ARCHGRP_L]

# Main component
lappend HIERARCHY(COMPONENTS) [list "TOPLEVEL" $CARD_BASE/src $ARCHGRP_ALL]

# XDC constraints for specific parts of the design
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/general.xdc"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/pcie.xdc"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/qsfp.xdc"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/ddr4.xdc"
if {$ETH_PORTS == 2} {
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/qsfp_fb2_only.xdc"
}
lappend SYNTH_FLAGS(CONSTR) [list "$CARD_BASE/constr/qsfp_loc.xdc" USED_IN implementation]
lappend SYNTH_FLAGS(CONSTR) [list "$CARD_BASE/constr/gty_10ge_ll.xdc" USED_IN implementation]
