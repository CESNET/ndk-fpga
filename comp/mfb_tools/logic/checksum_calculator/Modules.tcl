# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set COMP_BASE          "$ENTITY_BASE/comp"
set FIFO_BASE          "$OFM_PATH/comp/base/fifo"
set MFB_LOGIC_BASE     "$OFM_PATH/comp/mfb_tools/logic"
set MVB_TOOLS_BASE     "$OFM_PATH/comp/mvb_tools"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

lappend COMPONENTS [ list "MVB_AGGREGATE_LAST_VLD" "$MVB_TOOLS_BASE/aggregate/last_vld" "FULL" ]
lappend COMPONENTS [ list "CHSUM_REGIONAL"         "$COMP_BASE/chsum_regional"          "FULL" ]
lappend COMPONENTS [ list "CHSUM_FINALIZER"        "$COMP_BASE/chsum_finalizer"         "FULL" ]
lappend COMPONENTS [ list "FIFOX_MULTI"            "$FIFO_BASE/fifox_multi"             "FULL" ]
lappend COMPONENTS [ list "MFB_ITEMS_VLD"          "$MFB_LOGIC_BASE/items_vld"          "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/checksum_calculator.vhd"
# lappend MOD "$ENTITY_BASE/DevTree.tcl"
