# Modules.tcl: Local include script
# Copyright (C) 2021 CESNET
# Author: Radek Iša <isa@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET"        "$OFM_PATH/comp/uvm/reset"          "FULL"]
lappend COMPONENTS [list "COMMON"       "$OFM_PATH/comp/uvm/common"         "FULL"]
lappend COMPONENTS [list "MAC_SEG"      "$OFM_PATH/comp/uvm/intel_mac_seg"  "FULL"]
lappend COMPONENTS [list "LOGIC_VECTOR_ARRAY"   "$OFM_PATH/comp/uvm/logic_vector_array"     "FULL"]
lappend COMPONENTS [list "LOGIC_VECTOR" "$OFM_PATH/comp/uvm/logic_vector"   "FULL"]


lappend MOD "$ENTITY_BASE/pkg.sv"

