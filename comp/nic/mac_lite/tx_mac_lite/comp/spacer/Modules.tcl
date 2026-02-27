# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set CROSSBARX_BASE     "$OFM_PATH/comp/base/misc/crossbarx"
set SCHEDULER_TX_BASE  "$COMP_BASE/400g/scheduler_tx"

lappend COMPONENTS [list "TRANS_GEN"        "$ENTITY_BASE/comp/trans_gen"          "FULL" ]
# FIXME
#lappend COMPONENTS [list "GAP_COUNTER"      "$ENTITY_BASE/comp/gap_counter"        "FULL" ]
lappend COMPONENTS [list "PKT_PLANNER"      "$OFM_PATH/comp/base/misc/packet_planner"  "FULL" ]
lappend COMPONENTS [list "TRANS_FIFO"       "$CROSSBARX_BASE/comp/trans_fifo"      "FULL" ]
# FIXME
#lappend COMPONENTS [list "PCIE_BUFFER"      "$SCHEDULER_TX_BASE/comp/pcie_buf"     "FULL" ]
lappend COMPONENTS [list "CROSSBARX"        "$CROSSBARX_BASE"                      "FULL" ]
# FIXME
#lappend COMPONENTS [list "GMII_BUFFER"      "$SCHEDULER_TX_BASE/comp/gmii_buf"     "FULL" ]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/spacer.vhd"
