# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set MFB_FIFOX_BASE    "$OFM_PATH/comp/mfb_tools/storage/fifox"
set MFB_SPLITTER_BASE "$OFM_PATH/comp/mfb_tools/flow/splitter_simple"
set MFB_MERGER_BASE   "$OFM_PATH/comp/mfb_tools/flow/merger_simple"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "MFB_FIFOX"    $MFB_FIFOX_BASE    "FULL" ]
lappend COMPONENTS [ list "MFB_SPLITTER" $MFB_SPLITTER_BASE "FULL" ]
lappend COMPONENTS [ list "MFB_MERGER"   $MFB_MERGER_BASE   "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/mfb_switch_simple.vhd"
