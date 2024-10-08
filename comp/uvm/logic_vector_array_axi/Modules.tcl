# Modules.tcl: Local include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause
lappend COMPONENTS [list "RESET"              "$OFM_PATH/comp/uvm/reset"              "FULL"]
lappend COMPONENTS [list "LOGIC_VECTOR_ARRAY" "$OFM_PATH/comp/uvm/logic_vector_array" "FULL"]
lappend COMPONENTS [list "LOGIC_VECTOR"       "$OFM_PATH/comp/uvm/logic_vector"       "FULL"]
lappend COMPONENTS [list "AXI"                "$OFM_PATH/comp/uvm/axi"                "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
