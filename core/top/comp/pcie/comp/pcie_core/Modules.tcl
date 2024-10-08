# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set ASYNC_RESET_BASE   "$OFM_PATH/comp/base/async/reset"
set PCI_EXT_CAP_BASE   "$OFM_PATH/comp/pcie/common"
set PCIE_COMP_BASE     "$ENTITY_BASE/../"
set STREAMING_DBG_BASE "$OFM_PATH/comp/debug/streaming_debug"
set EVENT_COUNTER_BASE "$OFM_PATH/comp/base/misc/event_counter"
set MI_SPLITTER_BASE   "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set INTEL_BASE         "$ENTITY_BASE/../../../../.."
set MI_ASYNC_BASE      "$OFM_PATH/comp/mi_tools/async"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"
lappend PACKAGES "$INTEL_BASE/config/core_const.vhd"

# Components
lappend COMPONENTS [ list "ASYNC_RESET"  $ASYNC_RESET_BASE               "FULL" ]
lappend COMPONENTS [ list "PCI_EXT_CAP"  $PCI_EXT_CAP_BASE               "FULL" ]
lappend COMPONENTS [ list "PCIE_ADAPTER" "$PCIE_COMP_BASE/pcie_adapter"  "FULL" ]
lappend COMPONENTS [ list "DEBUG_PROBE"  $STREAMING_DBG_BASE             "FULL" ]
lappend COMPONENTS [ list "EVENT_CNT"    $EVENT_COUNTER_BASE             "FULL" ]
lappend COMPONENTS [ list "MI_SPLITTER"  $MI_SPLITTER_BASE               "FULL" ]
lappend COMPONENTS [ list "MI_ASYNC"     $MI_ASYNC_BASE                  "FULL" ]

lappend MOD "$ENTITY_BASE/pcie_core_ent.vhd"

# Source files for implemented component
if {$ARCHGRP == "P_TILE"} {
    lappend COMPONENTS [ list "PCIE_CII2CFG" "$PCIE_COMP_BASE/pcie_cii2cfg" "FULL" ]
    lappend MOD "$ENTITY_BASE/pcie_core_ptile.vhd"
} elseif {$ARCHGRP == "R_TILE"} {
    lappend COMPONENTS [ list "PCIE_CII2CFG" "$PCIE_COMP_BASE/pcie_cii2cfg" "FULL" ]
    lappend COMPONENTS [ list "PCIE_CRDT"    "$PCIE_COMP_BASE/pcie_crdt"    "FULL" ]
    lappend MOD "$ENTITY_BASE/pcie_core_rtile.vhd"
} elseif {$ARCHGRP == "H_TILE"} {
    lappend MOD "$ENTITY_BASE/pcie_core_htile.vhd"
} elseif {$ARCHGRP == "USP" || $ARCHGRP == "USP_PCIE4C" || $ARCHGRP == "USP_PCIE4"} {
    lappend MOD "$ENTITY_BASE/pcie_core_usp.vhd"
} else {
    lappend MOD "$ENTITY_BASE/pcie_core_empty.vhd"
}

lappend MOD "$ENTITY_BASE/DevTree.tcl"
