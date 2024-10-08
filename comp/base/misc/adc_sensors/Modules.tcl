#  Modules.tcl
#  Copyright (C) 2019 CESNET z. s. p. o.
#  Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
#
#  SPDX-License-Identifier: BSD-3-Clause

set MOD "$MOD $ENTITY_BASE/sensor_interface.vhd"

if { $ARCHGRP == "FULL" } {
    set MOD "$MOD $ENTITY_BASE/temp.ip"
    set MOD "$MOD $ENTITY_BASE/volt.ip"
    set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
    set MOD "$MOD $ENTITY_BASE/ver/tbench/adc_sim.vhd"
    set MOD "$MOD $ENTITY_BASE/sensor_interface_full.vhd"
} else {
    set MOD "$MOD $ENTITY_BASE/sensor_interface_empty.vhd"
}
