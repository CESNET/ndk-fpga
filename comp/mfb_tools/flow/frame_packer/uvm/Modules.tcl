# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): David Beneš <xbenes52@vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

# Set paths

lappend COMPONENTS [ list "SV_MVB_UVM_BASE"            "$OFM_PATH/comp/uvm/mvb"                    "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_MVB"        "$OFM_PATH/comp/uvm/logic_vector_mvb"       "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR"            "$OFM_PATH/comp/uvm/logic_vector"           "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY"      "$OFM_PATH/comp/uvm/logic_vector_array"     "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY_MFB"  "$OFM_PATH/comp/uvm/logic_vector_array_mfb" "FULL"]
lappend COMPONENTS [ list "SV_PROBE_UVM"               "$OFM_PATH/comp/uvm/probe"                  "FULL"]

lappend MOD "$ENTITY_BASE/tbench/info/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/property.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
