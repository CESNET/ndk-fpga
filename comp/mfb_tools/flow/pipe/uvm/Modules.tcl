# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author:   David Beneš <xbenes52@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

lappend COMPONENTS [ list "SV_MFB_UVM_BASE"     "$OFM_PATH/comp/uvm/mfb"                     "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR"     "$OFM_PATH/comp/uvm/logic_vector"            "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_MFB" "$OFM_PATH/comp/uvm/logic_vector_array_mfb"  "FULL"]


lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/property.sv"
lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"

