# Modules.tcl: Local include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kriz <danielkriz@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET"              "$OFM_PATH/comp/uvm/reset"              "FULL"]
lappend COMPONENTS [list "LOGIC_VECTOR_ARRAY" "$OFM_PATH/comp/uvm/logic_vector_array" "FULL"]
lappend COMPONENTS [list "LOGIC_VECTOR"       "$OFM_PATH/comp/uvm/logic_vector"       "FULL"]
lappend COMPONENTS [list "AVST"               "$OFM_PATH/comp/uvm/avst"               "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
