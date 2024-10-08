# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author:   Daniel Kříž <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

lappend COMPONENTS [ list "SV_MFB_UVM_BASE"             "$OFM_PATH/comp/uvm/mfb"                      "FULL"]
lappend COMPONENTS [ list "SV_AVST_UVM_BASE"            "$OFM_PATH/comp/uvm/avst"                     "FULL"]
lappend COMPONENTS [ list "SV_AXI_UVM_BASE"             "$OFM_PATH/comp/uvm/axi"                      "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY"       "$OFM_PATH/comp/uvm/logic_vector_array"       "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR"             "$OFM_PATH/comp/uvm/logic_vector"             "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY_MFB"   "$OFM_PATH/comp/uvm/logic_vector_array_mfb"   "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY_AVST"  "$OFM_PATH/comp/uvm/logic_vector_array_avst"  "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY_AXI"   "$OFM_PATH/comp/uvm/logic_vector_array_axi"   "FULL"]

lappend COMPONENTS [ list "SV_CRDT_AGENT_UVM" "$ENTITY_BASE/tbench/env/crdt_agent" "FULL" ]

lappend MOD "$OFM_PATH/comp/base/pkg/pcie_meta_pack.sv"

lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
