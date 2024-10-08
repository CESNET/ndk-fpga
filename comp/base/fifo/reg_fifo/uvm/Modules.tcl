# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>

# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE             "$OFM_PATH/comp/uvm"
set SV_MVB_PIPE_UVM_BASE    "$OFM_PATH/comp/mvb_tools/flow/pipe/uvm"

lappend COMPONENTS [ list "SV_RESET"                "$SV_UVM_BASE/reset"            "FULL"]
lappend COMPONENTS [ list "SV_MVB_UVM"              "$SV_UVM_BASE/mvb"              "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_MVB_UVM" "$SV_UVM_BASE/logic_vector_mvb" "FULL"]
lappend COMPONENTS [ list "SV_MVB_PIPE_UVM"         "$SV_MVB_PIPE_UVM_BASE"         "FULL"]

lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/property.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
