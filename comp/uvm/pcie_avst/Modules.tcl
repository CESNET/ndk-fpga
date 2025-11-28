# Modules.tcl: Local include script
# Copyright (C) 2025 CESNET
# Author: Radek Iša <isa@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET" "$OFM_PATH/comp/uvm/reset" "FULL"]
lappend COMPONENTS [list "AXI"   "$OFM_PATH/comp/uvm/avst"  "FULL"]
lappend COMPONENTS [list "PCIE"  "$OFM_PATH/comp/uvm/pcie"  "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
