# Quartus.inc.tcl: Quartus.tcl include for card
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NDK constants (populates all NDK variables from env)
source $env(CORE_BASE)/config/core_bootstrap.tcl

# Include common card script
source $CORE_BASE/Quartus.inc.tcl

# Propagating card constants to the Modules.tcl files of the underlying components.
# The description of usage of this array is provided in the Parametrization section
# of the NDK-CORE repository.
set CARD_ARCHGRP(CORE_BASE)          $CORE_BASE
set CARD_ARCHGRP(IP_BUILD_DIR)       $CARD_BASE/src/ip
set CARD_ARCHGRP(PCIE_ENDPOINT_MODE) $PCIE_ENDPOINT_MODE
set CARD_ARCHGRP(PCIE_GEN)           $PCIE_GEN
set CARD_ARCHGRP(NET_MOD_ARCH)       $NET_MOD_ARCH
# Second dimension because of addition of an element of another array, just for clarity.
set CARD_ARCHGRP(ETH_PORT_SPEED,0)   $ETH_PORT_SPEED(0)
set CARD_ARCHGRP(ETH_PORT_CHAN,0)    $ETH_PORT_CHAN(0)
set CARD_ARCHGRP(EHIP_PORT_TYPE,0)   $EHIP_PORT_TYPE(0)

# select fpga name
if {$BOARD_VARIANT == 0} {
    set CARD_FPGA "AGIB023R18A1E1V"
} elseif {$BOARD_VARIANT == 1} {
    set CARD_FPGA "AGIB023R18A1E1VC"
} else {
    error "Unsupported BOARD_VARIANT=$BOARD_VARIANT! Supported values are:
- 0 for board with AGIB023R18A1E1V,
- 1 for board with AGIB023R18A1E1VC."
}

set CARD_ARCHGRP(FPGA)               $CARD_FPGA

# make lists from associative arrays
set CARD_ARCHGRP_L [array get CARD_ARCHGRP]
set CORE_ARCHGRP_L [array get CORE_ARCHGRP]

# concatenate lists to be handed as a part of the ARCHGRP to the TOPLEVEL
set ARCHGRP_ALL [concat $CARD_ARCHGRP_L $CORE_ARCHGRP_L]

# Main component
lappend HIERARCHY(COMPONENTS) \
    [list "TOPLEVEL" $CARD_BASE/src $ARCHGRP_ALL]

# Design parameters
set SYNTH_FLAGS(MODULE)    "FPGA"
set SYNTH_FLAGS(FPGA)      $CARD_FPGA
set SYNTH_FLAGS(BITSTREAM) "RBF"

# Enable Quartus Support-Logic Generation stage
set SYNTH_FLAGS(QUARTUS_TLG) 1

# QSF constraints for specific parts of the design
if {$BOARD_VARIANT == 0} {
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/device_var0.qsf"
}
if {$BOARD_VARIANT == 1} {
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/device_var1.qsf"
}
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/general.qsf"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/bmc.qsf"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/pcie.qsf"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/qsfp.qsf"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/ddr4.qsf"
lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/timing.sdc"
