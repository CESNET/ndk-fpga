# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_UVM_BASE "$OFM_PATH/comp/uvm"

# Define components
lappend COMPONENTS [ list "SV_RESET"            "$SV_UVM_BASE/reset"            "FULL" ] \
                   [ list "SV_LOGIC_VECTOR_MVB" "$SV_UVM_BASE/logic_vector_mvb" "FULL" ]

# Define modules
lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"   \
            "$ENTITY_BASE/tbench/tests/pkg.sv" \
            "$ENTITY_BASE/tbench/property.sv"  \
            "$ENTITY_BASE/tbench/dut.sv"       \
            "$ENTITY_BASE/tbench/testbench.sv"
