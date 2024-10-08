# Modules.tcl: Local include script
# Copyright (C) 2021 CESNET
# Author: Radek Iša <isa@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "COMMON"     "$OFM_PATH/comp/uvm/common"     "FULL"]

lappend MOD "$ENTITY_BASE/interface.sv"
lappend MOD "$ENTITY_BASE/pkg.sv"

