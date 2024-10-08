# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FL_BASE             "$OFM_PATH/comp/fl_tools"
set FL_DFIFO_BASE       "$FL_BASE/storage/dfifo"

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"


set MOD "$MOD $ENTITY_BASE/switch_ent.vhd"
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"

if { $ARCHGRP == "FULL" } {

    set COMPONENTS [list                                        \
        [list "FL_DFIFO"  $FL_DFIFO_BASE "FULL"]                \
    ]

    set MOD "$MOD $ENTITY_BASE/ifnum_extract.vhd"
    set MOD "$MOD $ENTITY_BASE/tx_out.vhd"
    set MOD "$MOD $ENTITY_BASE/tx_out_array.vhd"
    set MOD "$MOD $ENTITY_BASE/switch_impl_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/switch_impl_fifo.vhd"
    set MOD "$MOD $ENTITY_BASE/switch_impl_nofifo.vhd"
    set MOD "$MOD $ENTITY_BASE/switch.vhd"
#    set MOD "$MOD $ENTITY_BASE/top/switch_1to4_fl64.vhd"

}

if { $ARCHGRP == "EMPTY" } {

    set MOD "$MOD $ENTITY_BASE/switch_empty.vhd"

}
