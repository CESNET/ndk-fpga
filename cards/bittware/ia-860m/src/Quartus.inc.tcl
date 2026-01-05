# Quartus.inc.tcl: Quartus.tcl include for Bittware IA-860m card
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# NDK constants (populates all NDK variables from env)
source $env(CORE_BASE)/config/core_bootstrap.tcl

# Include card common script
source $CORE_BASE/Quartus.inc.tcl

# Propagating card constants to the Modules.tcl files of the underlying components.
# The description of usage of this array is provided in the Parametrization section
# of the NDK-CORE repository.
set CARD_ARCHGRP(CORE_BASE)          $CORE_BASE
set CARD_ARCHGRP(IP_BUILD_DIR)       $CARD_BASE/src/ip
set CARD_ARCHGRP(NET_MOD_ARCH)       $NET_MOD_ARCH
set CARD_ARCHGRP(PCIE_ENDPOINT_MODE) $PCIE_ENDPOINT_MODE
set CARD_ARCHGRP(PCIE_GEN)           $PCIE_GEN
# Second dimension because of addition of an element of another array, just for clarity.
set CARD_ARCHGRP(ETH_PORTS)          $ETH_PORTS
set CARD_ARCHGRP(ETH_PORT_SPEED,0)   $ETH_PORT_SPEED(0)
set CARD_ARCHGRP(ETH_PORT_CHAN,0)    $ETH_PORT_CHAN(0)
set CARD_ARCHGRP(EHIP_PORT_TYPE,0)   $EHIP_PORT_TYPE(0)
set CARD_ARCHGRP(ETH_PORT_SPEED,1)   $ETH_PORT_SPEED(1)
set CARD_ARCHGRP(ETH_PORT_CHAN,1)    $ETH_PORT_CHAN(1)
set CARD_ARCHGRP(EHIP_PORT_TYPE,1)   $EHIP_PORT_TYPE(1)
if {$ETH_PORTS == 3} {
    set CARD_ARCHGRP(ETH_PORT_SPEED,2)   $ETH_PORT_SPEED(2)
    set CARD_ARCHGRP(ETH_PORT_CHAN,2)    $ETH_PORT_CHAN(2)
    set CARD_ARCHGRP(EHIP_PORT_TYPE,2)   $EHIP_PORT_TYPE(2)
}


# select fpga name, Revision 4, Revision 0,1,3 uses AGMF039R47A2E2VR0
if {$BOARD_VARIANT == 0 || $BOARD_VARIANT == 1 || $BOARD_VARIANT == 2 || $BOARD_VARIANT == 3} {
    set CARD_FPGA "AGMF039R47A2E2VR0"
} elseif {$BOARD_VARIANT == 4} {
    set CARD_FPGA "AGMF039R47A1E2VC"
} else {
    error "Unsupported BOARD_VARIANT=$BOARD_VARIANT! Supported values are:
- 0,1,2,3 for board with AGMF039R47A2E2VR0,
- 4 for board with AGMF039R47A1E2VC."
}

set CARD_ARCHGRP(FPGA) $CARD_FPGA

set CARD_ARCHGRP(BMC_CTRL_ARCH) "EMPTY"
if {$BMC_ENABLE} {
    set CARD_ARCHGRP(BMC_CTRL_ARCH) "FULL"
}

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
# Enable automatic clear old IP files before IP Generation
set SYNTH_FLAGS(IP_FILES_CLEAN_ENABLE) 1

# QSF constraints for specific parts of the design
if {$BOARD_VARIANT == 0 || $BOARD_VARIANT == 1 || $BOARD_VARIANT == 2} {
    # Old BMC connections and ES chip
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/device_var0.qsf"
}
if {$BOARD_VARIANT == 3} {
    # New BMC connections and ES chip
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/device_var3.qsf"
}
if {$BOARD_VARIANT == 4} {
    # New BMC connections and production chip
    lappend SYNTH_FLAGS(CONSTR) "$CARD_BASE/constr/device_var4.qsf"
}

set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/general.qsf"
#set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/bmc.qsf" # BMC is different for revsion 0,1 and 3,4
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie.qsf"

if {$ETH_PORTS == 3} {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/qsfp_3ports.qsf"
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/timing_3ports.sdc"
} elseif {$ETH_PORTS == 2} {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/qsfp_2ports.qsf"
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/timing_2ports.sdc"
} else {
    error "Unsupported ETH_PORTS=$ETH_PORTS! Supported values are 2 and 3."
}

