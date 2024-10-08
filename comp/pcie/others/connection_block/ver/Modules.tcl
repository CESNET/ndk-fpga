# Modules.tcl: Local include script
# Copyright (C) 2020 CESNET
# Author: Radek Iša <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set COMPONENTS [ list \
    [list "MFB_VER"  "$OFM_PATH/comp/mfb_tools/ver_uvm"   "FULL"]\
    [list "AVST_VER" "$FIRMWARE_BASE/comp/avst_tools/ver_uvm"  "FULL"]\
]

lappend MOD "$ENTITY_BASE/tbench/dut.sv"
lappend MOD "$ENTITY_BASE/tbench/env/pkg.sv"
lappend MOD "$ENTITY_BASE/tbench/test/pkg.sv"
