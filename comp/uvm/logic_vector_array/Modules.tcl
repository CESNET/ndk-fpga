# Modules.tcl: Local include script
# Copyright (C) 2021 CESNET
# Author: Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend MOD "$ENTITY_BASE/pkg.sv"
lappend COMPONENTS \
    [list "RESET"       "$OFM_PATH/comp/uvm/reset"                  "FULL"] \
