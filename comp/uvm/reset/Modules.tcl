# Modules.tcl:  Local include script for reset agent
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Radek Iša <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "COMMON"          "$OFM_PATH/comp/uvm/common"         "FULL"]

lappend MOD "$ENTITY_BASE/interface.sv"
lappend MOD "$ENTITY_BASE/pkg.sv"

