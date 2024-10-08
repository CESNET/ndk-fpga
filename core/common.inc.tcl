# common.inc.tcl: including of constants to the prerequisities
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#           Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SYNTH_FLAGS(OUTPUT) $OUTPUT_NAME

# Propagate CORE constants to Modules.tcl files of the underlying components through
# an associative array. For more detailed description of how pass parameters to this array,
# see the configuration section of the NDK-CORE repository documentation.
set CORE_ARCHGRP(CLOCK_GEN_ARCH)                $CLOCK_GEN_ARCH
set CORE_ARCHGRP(PCIE_MOD_ARCH)                 $PCIE_MOD_ARCH
set CORE_ARCHGRP(NET_MOD_ARCH)                  $NET_MOD_ARCH
set CORE_ARCHGRP(SDM_SYSMON_ARCH)               $SDM_SYSMON_ARCH
set CORE_ARCHGRP(DMA_TYPE)                      $DMA_TYPE
set CORE_ARCHGRP(APPLICATION_CORE_ENTITY_ONLY)  false
set CORE_ARCHGRP(VIRTUAL_DEBUG_ENABLE)          $VIRTUAL_DEBUG_ENABLE

# Prerequisites for generated VHDL package
set UCP_PREREQ [list $CARD_CONST $CORE_CONF $CARD_CONF [expr {[info exists APP_CONF] ? $APP_CONF : ""}]]

# Let generate package from configuration files and add it to project
lappend HIERARCHY(PACKAGES) [nb_generate_file_register_userpkg "combo_user_const" "" $UCP_PREREQ]

# Let generate DevTree.vhd and add it to project
lappend HIERARCHY(PACKAGES) [nb_generate_file_register_devtree]

# For cocotb run, append runtime environment to system path
if {![info exists env(PYTHONPATH)] || [string first "$CORE_BASE/cocotb" $env(PYTHONPATH)] == -1} {
    append env(PYTHONPATH) ":$CORE_BASE/cocotb"
}

# ----- Default target: synthesis of the project ------------------------------
proc target_default {} {
    global SYNTH_FLAGS HIERARCHY
    SynthesizeProject SYNTH_FLAGS HIERARCHY
}
