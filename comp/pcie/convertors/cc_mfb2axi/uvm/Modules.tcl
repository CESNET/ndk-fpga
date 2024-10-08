# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author:   Daniel Kříž <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

lappend COMPONENTS [ list "SV_MFB_UVM_BASE"        "$OFM_PATH/comp/uvm/mfb"                         "FULL"]
lappend COMPONENTS [ list "SV_AXI_UVM_BASE"        "$OFM_PATH/comp/uvm/axi"                         "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTROR_ARRAY" "$OFM_PATH/comp/uvm/logic_vector_array"          "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTROR_MFB"   "$OFM_PATH/comp/uvm/logic_vector_array_mfb"      "FULL"]
lappend COMPONENTS [ list "SV_LOGIC_VECTROR_AXI"   "$OFM_PATH/comp/uvm/logic_vector_array_axi"      "FULL"]
lappend COMPONENTS [ list "MODEL_MFB2AVST_CONVERTOR"     "$OFM_PATH/comp/pcie/others/mfb2avst/uvm"     "FULL"]


lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/tests/pkg.sv"

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/testbench.sv"
