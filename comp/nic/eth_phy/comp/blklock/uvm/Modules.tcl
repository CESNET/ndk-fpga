# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE               "$OFM_PATH/comp/uvm"

lappend COMPONENTS [ list "SV_MFB_UVM_BASE"             "$SV_UVM_BASE/mvb"              "FULL"]
lappend COMPONENTS [ list "SV_RESET_UVM_BASE"           "$SV_UVM_BASE/reset"            "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_UVM_BASE"    "$SV_UVM_BASE/logic_vector"     "FULL"]

lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
