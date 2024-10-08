# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE    "$OFM_PATH/comp/uvm"

lappend COMPONENTS [ list "SV_MFB_UVM_BASE"              "$SV_UVM_BASE/mfb"               "FULL"]
lappend COMPONENTS [ list "SV_MVB_UVM_BASE"              "$SV_UVM_BASE/mvb"               "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_MVB"          "$SV_UVM_BASE/logic_vector_mvb"  "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY_MFB"    "$SV_UVM_BASE/logic_vector_array_mfb"   "FULL"]
lappend COMPONENTS [ list "MI"                           "$SV_UVM_BASE/mi"               "FULL"]

set MOD "$MOD $ENTITY_BASE/tbench/env/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/tests/pkg.sv"

set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/testbench.sv"
