# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE                "$OFM_PATH/comp/base/pkg"
set CHECKSUM_CALC_BASE      "$OFM_PATH/comp/mfb_tools/logic/checksum_calculator"
set METADATA_INSERTOR_BASE  "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MFB_DUPLICATION_BASE    "$OFM_PATH/comp/mfb_tools/flow/duplication"
set MVB_MERGE_ITEMS_BASE    "$OFM_PATH/comp/mvb_tools/flow/merge_items"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

lappend COMPONENTS [ list "CHECKSUM_CALCULATOR"   $CHECKSUM_CALC_BASE     "FULL" ]
lappend COMPONENTS [ list "METADATA_INSERTOR"     $METADATA_INSERTOR_BASE "FULL" ]
lappend COMPONENTS [ list "MFB_DUPLICATION"       $MFB_DUPLICATION_BASE   "FULL" ]
lappend COMPONENTS [ list "MVB_MERGE_ITEMS"       $MVB_MERGE_ITEMS_BASE   "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/checksum_l3.vhd"
lappend MOD "$ENTITY_BASE/checksum_l4.vhd"
lappend MOD "$ENTITY_BASE/checksum_l3l4.vhd"
