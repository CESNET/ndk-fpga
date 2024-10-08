# Modules.tcl: include script for mi agent
# Copyright (C) 2021 CESNET
# Author: Radek Iša <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET"        "$OFM_PATH/comp/uvm/reset"        "FULL"]


lappend MOD "$ENTITY_BASE/interface.sv"
lappend MOD "$ENTITY_BASE/pkg.sv"
