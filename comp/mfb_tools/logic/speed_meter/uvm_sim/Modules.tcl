# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author:   Daniel Kříž <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

lappend COMPONENTS [ list "SV_MVB_UVM_BASE"            "$OFM_PATH/comp/uvm/mvb"                    "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTROR_ARRAY"     "$OFM_PATH/comp/uvm/logic_vector_array"     "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTROR_ARRAY_MFB" "$OFM_PATH/comp/uvm/logic_vector_array_mfb" "FULL"]
lappend COMPONENTS [ list "SV_MI"                      "$OFM_PATH/comp/uvm/mi"                     "FULL"]


lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
