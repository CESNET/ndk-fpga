# Modules.tcl: Local include Modules script
# Copyright (C) 2020 CESNET
# Author: Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set COMPONENTS [list \
    [list "NDP"    $OFM_PATH/comp/ver/ndp        "FULL"] \
    [list "AVALON" $OFM_PATH/comp/ver/avst       "FULL"] \
    [list "AXI"    $OFM_PATH/comp/ver/axi        "PCIE"] \
]

if { $ARCHGRP == "FULL" } {
    lappend MOD "$ENTITY_BASE/sv_pcie_pkg.sv"
}
