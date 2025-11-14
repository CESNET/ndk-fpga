# Modules.tcl:
# Copyright (C) 2025 CESNET
# Author: Radek Iša <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET"              "$OFM_PATH/comp/uvm/reset"              "FULL"]
lappend COMPONENTS [list "COMMON"             "$OFM_PATH/comp/uvm/common"             "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
