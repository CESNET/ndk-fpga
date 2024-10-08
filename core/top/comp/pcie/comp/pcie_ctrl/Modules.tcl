# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set MTC_BASE          "$OFM_PATH/comp/pcie/mtc"
set PTC_BASE          "$OFM_PATH/comp/pcie/ptc"
set MFB_MERGER_BASE   "$OFM_PATH/comp/mfb_tools/flow/merger_simple"
set MFB_SPLITTER_BASE "$OFM_PATH/comp/mfb_tools/flow/splitter_simple"
set MI_ASYNC_BASE     "$OFM_PATH/comp/mi_tools/async"
set MI_PIPE_BASE      "$OFM_PATH/comp/mi_tools/pipe"
set MI_SPLITTER_BASE  "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set STREAMIN_DBG_BASE "$OFM_PATH/comp/debug/streaming_debug"
set INTEL_BASE        "$ENTITY_BASE/../../../../.."

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"
lappend PACKAGES "$INTEL_BASE/config/core_const.vhd"

# Components
lappend COMPONENTS [ list "MTC"          $MTC_BASE          "FULL" ]
lappend COMPONENTS [ list "PTC"          $PTC_BASE          "FULL" ]
lappend COMPONENTS [ list "MFB_MERGER"   $MFB_MERGER_BASE   "FULL" ]
lappend COMPONENTS [ list "MFB_SPLITTER" $MFB_SPLITTER_BASE "FULL" ]
lappend COMPONENTS [ list "MI_ASYNC"     $MI_ASYNC_BASE     "FULL" ]
lappend COMPONENTS [ list "MI_PIPE"      $MI_PIPE_BASE      "FULL" ]
lappend COMPONENTS [ list "MI_SPLITTER"  $MI_SPLITTER_BASE  "FULL" ]
lappend COMPONENTS [ list "DEBUG_PROBE"  $STREAMIN_DBG_BASE "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/pcie_ctrl.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
