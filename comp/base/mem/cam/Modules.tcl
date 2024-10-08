# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set CARRY_BASE    "$OFM_PATH/comp/base/logic/carry_chain"
set DEC_MODULE    "$OFM_PATH/comp/base/logic/dec1fn/dec1fn_enable.vhd"

set MOD "$MOD $DEC_MODULE"
set PKG_BASE "$OFM_PATH/comp/base/pkg"
set COMPONENTS [list \
    [ list "PKG"        $PKG_BASE          "MATH"] \
    [ list "CARRY"      $CARRY_BASE        "FULL"] \
]

if { $ARCHGRP == "LIGHT" } {
    #lightweight version of CAM made of registers
    set MOD "$MOD $ENTITY_BASE/cam_light_2port.vhd"
    set MOD "$MOD $ENTITY_BASE/cam_light.vhd"
} else {
    set MOD "$MOD $ENTITY_BASE/cam_fill_element.vhd"
    set MOD "$MOD $ENTITY_BASE/cam_filling_part.vhd"
    set MOD "$MOD $ENTITY_BASE/cam_row.vhd"
    set MOD "$MOD $ENTITY_BASE/cam_data_array.vhd"
    set MOD "$MOD $ENTITY_BASE/cam.vhd"
}
