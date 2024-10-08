# Modules.tcl: Local include script
# Copyright (C) 2021 CESNET
# Author: Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS \
    [list "COMMON"       "$OFM_PATH/comp/uvm/common"                  "FULL"] \
    [list "BYTE_ARRAY"   "$OFM_PATH/comp/uvm/byte_array"              "FULL"] \
    [list "LII"          "$OFM_PATH/comp/uvm/lii"                     "FULL"] \
    [list "LOGIC_VECTOR" "$OFM_PATH/comp/uvm/logic_vector"            "FULL"] \

lappend MOD "$ENTITY_BASE/pkg.sv"
