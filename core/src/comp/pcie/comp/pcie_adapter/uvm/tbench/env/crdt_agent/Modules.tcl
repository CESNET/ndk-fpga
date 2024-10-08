# Modules.tcl: Local include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kriz <danielkriz@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "RESET"        "$OFM_PATH/comp/uvm/reset"          "FULL"]
lappend COMPONENTS [list "COMMON"       "$OFM_PATH/comp/uvm/common"         "FULL"]


lappend MOD "$ENTITY_BASE/interface.sv"
lappend MOD "$ENTITY_BASE/pkg.sv"
