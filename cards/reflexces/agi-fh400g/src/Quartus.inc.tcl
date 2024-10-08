# Quartus.inc.tcl: Quartus.tcl include for XpressSX AGI-FH400G
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#           Vladislav Valek <valekv@cesnet.cz>
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
# Second dimension because of addition of an element of another array, just for clarity.
set CARD_ARCHGRP(ETH_PORT_SPEED,0)   $ETH_PORT_SPEED(0)
set CARD_ARCHGRP(ETH_PORT_CHAN,0)    $ETH_PORT_CHAN(0)
set CARD_ARCHGRP(EHIP_PORT_TYPE,0)   $EHIP_PORT_TYPE(0)

# select fpga name
set CARD_FPGA ""
if {$BOARD_REV == 0} {
    # first prototypes
    set CARD_FPGA "AGIB027R29A1E2VR0"
} elseif {$BOARD_REV == 1} {
    set CARD_FPGA "AGIB027R29A1E2VR3"
} elseif {$BOARD_REV == 2} {
    set CARD_FPGA "AGIB027R29A1E2V"
} else {
    error "Unsupported BOARD_REV=$BOARD_REV! Supported values are: 0, 1 or 2."
}
set CARD_ARCHGRP(FPGA) $CARD_FPGA

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
set SYNTH_FLAGS(CONSTR) ""
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/timing.sdc"
if {$BOARD_REV == 0} {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/device_r0.qsf"
}
if {$BOARD_REV == 1} {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/device_r3.qsf"
}
if {$BOARD_REV == 2} {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/device.qsf"
}
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/general.qsf"
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/hps.qsf"
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/sodimm.qsf"
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie_misc.qsf"
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie0.qsf"
set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/qsfp_misc.qsf"

if {$EHIP_PORT_TYPE(0) == 1} {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/multirate.qsf"
}

if {$PCIE_ENDPOINT_MODE == 1} {
    set PCIE_HIPS [expr $PCIE_ENDPOINTS/2]
} else {
    set PCIE_HIPS $PCIE_ENDPOINTS
}

if {$PCIE_HIPS == 2} {
    if {$TEST_FW_PCIE1_ONBOARD_DDR4} {
        set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie1.qsf"
        set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie2_virtual.qsf"
    } else {
        set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie2.qsf"
        set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie1_virtual.qsf"
    }
} else {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie1_virtual.qsf"
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/pcie2_virtual.qsf"
}

if {$NET_MOD_ARCH == "F_TILE"} {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/qsfp.qsf"
} else {
    set SYNTH_FLAGS(CONSTR) "$SYNTH_FLAGS(CONSTR) $CARD_BASE/constr/qsfp_virtual.qsf"
}
