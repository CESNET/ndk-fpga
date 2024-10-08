# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Tomas Hak <xhakto01@vut.cz>

# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE "$OFM_PATH/comp/uvm"

lappend COMPONENTS [ list "SV_RESET"                  "$SV_UVM_BASE/reset"                  "FULL"]
lappend COMPONENTS [ list "SV_MI_UVM_BASE"            "$SV_UVM_BASE/mi"                     "FULL"]
lappend COMPONENTS [ list "SVM_UVM_COMMON"            "$SV_UVM_BASE/common"                 "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY_MFB" "$SV_UVM_BASE/logic_vector_array_mfb" "FULL"]

lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/property.sv"
lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
