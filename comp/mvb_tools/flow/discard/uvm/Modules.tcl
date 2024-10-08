# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author:   Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

lappend COMPONENTS [ list "SV_MVB_UVM_BASE"      "$OFM_PATH/comp/uvm/mvb"          "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTROR"     "$OFM_PATH/comp/uvm/logic_vector" "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTROR_MVB" "$OFM_PATH/comp/uvm/logic_vector_mvb"          "FULL"]

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut_wrapper.vhd"
lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
