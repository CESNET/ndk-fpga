# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FL_BASE             "$OFM_PATH/comp/fl_tools"
set FL_FIFO_BASE        "$FL_BASE/storage/fifo"
set DEC_BASE            "$OFM_PATH/comp/base/logic/dec1fn"

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"


set MOD "$MOD $ENTITY_BASE/distributor_ent.vhd"
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"

if { $ARCHGRP == "FULL" } {

    set COMPONENTS [list                                        \
        [list "FL_FIFO"  $FL_FIFO_BASE "FULL"]                  \
        [list "DEC"      $DEC_BASE     "FULL"]                  \
    ]

    set MOD "$MOD $ENTITY_BASE/distributor_out.vhd"
    set MOD "$MOD $ENTITY_BASE/distributor_ifsel_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/inum_extract.vhd"
    set MOD "$MOD $ENTITY_BASE/distributor_ifsel_word0.vhd"
    set MOD "$MOD $ENTITY_BASE/distributor_ifsel_word_non0.vhd"
    set MOD "$MOD $ENTITY_BASE/distributor.vhd"
#    set MOD "$MOD $ENTITY_BASE/top/distributor_fl64.vhd"

}

if { $ARCHGRP == "EMPTY" } {

    set MOD "$MOD $ENTITY_BASE/distributor_empty.vhd"

}
