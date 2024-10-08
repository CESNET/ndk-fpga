# Modules.tcl: Local include script
# Copyright (C) 2022 CESNET
# Author: Daniel Kříž <xkrizd01@vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET"           "$OFM_PATH/comp/uvm/reset"          "FULL"]
lappend COMPONENTS [list "COMMON"          "$OFM_PATH/comp/uvm/common"         "FULL"]
lappend COMPONENTS [list "LOGIC_VECTOR"    "$OFM_PATH/comp/uvm/logic_vector"   "FULL"]
lappend COMPONENTS [list "MVB"             "$OFM_PATH/comp/uvm/mvb"            "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
