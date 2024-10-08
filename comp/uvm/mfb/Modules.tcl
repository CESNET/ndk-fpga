# Modules.tcl: Local include script
# Copyright (C) 2021 CESNET
# Author: Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET"        "$OFM_PATH/comp/uvm/reset"          "FULL"]
lappend COMPONENTS [list "COMMON"       "$OFM_PATH/comp/uvm/common"         "FULL"]


lappend MOD "$ENTITY_BASE/interface.sv"
lappend MOD "$ENTITY_BASE/property.sv"
lappend MOD "$ENTITY_BASE/pkg.sv"
