# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2015 CESNET
# Copyright (C) 2024 BrnoLogic
# Author: Lukas Kekely <kekely@cesnet.cz>
#         Vlastimil Kosar <kosar@brnologic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

set ASYNC_BASE          "$OFM_PATH/comp/base/async/"
set MI_TOOLS_BASE       "$OFM_PATH/comp/mi_tools"
set MGMT_BASE           "$OFM_PATH/comp/nic/eth_phy/comp/mgmt"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "MI_SPLITTER_PLUS_GEN"  "$MI_TOOLS_BASE/splitter_plus_gen" "FULL"]
lappend COMPONENTS [list "MGMT"                  "$MGMT_BASE"                       "FULL"]
lappend COMPONENTS [list "ASYNC_RESET"           "$ASYNC_BASE/reset"                "FULL"]
lappend COMPONENTS [list "ASYNC_OPEN_LOOP"       "$ASYNC_BASE/open_loop"            "FULL"]

# Uncomment only for local synthesis
#lappend MOD "$ENTITY_BASE/usp_pcspma_10g.xci"

lappend MOD "$ENTITY_BASE/../40ge/comp/pcs/ber_mon.vhd"
lappend MOD "$ENTITY_BASE/usp_phyx4_10g_25g.vhd"

## EARLY order won't work as there are no clocks created in that moment
lappend SRCS(CONSTR_VIVADO) [list "$ENTITY_BASE/usp_phyx4_10g_25g.xdc" \
    SCOPED_TO_REF USP_PCS_PMA_WRAPPER \
    PROCESSING_ORDER LATE \
    VIVADO_SET_PROPERTY [list used_in_implementation true] \
    VIVADO_SET_PROPERTY [list used_in_synthesis false] \
]
