# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Radek Iša <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set UVM_PATH                  "$OFM_PATH/comp/uvm"
set SV_MVB_PIPE_UVM_BASE      "$OFM_PATH/comp/mvb_tools/flow/pipe/uvm"


lappend COMPONENTS [ list "SV_COMMON"                 "$UVM_PATH/common"                   "FULL"]
lappend COMPONENTS [ list "SV_RESET"                  "$UVM_PATH/reset"                    "FULL"]
lappend COMPONENTS [ list "SV_BYTE_ARRAY_MFB"         "$UVM_PATH/byte_array_mfb"           "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTOR_ARRAY_MFB" "$UVM_PATH/logic_vector_array_mfb"   "FULL"]
lappend COMPONENTS [ list "SV_MVB"                    "$UVM_PATH/mvb"                      "FULL"]
lappend COMPONENTS [ list "SV_MI"                     "$UVM_PATH/mi"                       "FULL"]
lappend COMPONENTS [ list "SV_PROBE_UVM"              "$UVM_PATH/probe"                    "FULL"]

lappend MOD "$OFM_PATH/comp/base/pkg/pcie_meta_pack.sv"

lappend MOD "$ENTITY_BASE/tbench/rx_env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/property.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
