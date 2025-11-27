# Modules.tcl: Local include script
# Copyright (C) 2025 CESNET
# Author: Radek Iša <isa@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.sv"


# TODO: REMOVE THIS IF POSSIBLE IN FUTURE
# ADD XILINX PCIE FUNCTION
lappend COMPONENTS [list "PCIE_AXI" "$OFM_PATH/comp/uvm/pcie_axi" "FULL"]
# ADD INTEL PCIE FUNCTION
lappend COMPONENTS [list "PCIE_AVST" "$OFM_PATH/comp/uvm/pcie_avst" "FULL"]
# TODO: REMOVE THIS IF POSSIBLE IN FUTURE
lappend COMPONENTS [list "LVA_MFB" "$OFM_PATH/comp/uvm/logic_vector_array_mfb"   "FULL"]
lappend COMPONENTS [list "LV_MVB"  "$OFM_PATH/comp/uvm/logic_vector_mvb"         "FULL"]

lappend COMPONENTS [list "RESET" "$OFM_PATH/comp/uvm/reset" "FULL"]
lappend COMPONENTS [list "MFB"   "$OFM_PATH/comp/uvm/mfb"   "FULL"]
lappend COMPONENTS [list "MVB"   "$OFM_PATH/comp/uvm/mvb"   "FULL"]
lappend COMPONENTS [list "PCIE"  "$OFM_PATH/comp/uvm/pcie"  "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
