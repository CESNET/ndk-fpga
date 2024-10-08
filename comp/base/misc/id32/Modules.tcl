# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set IM_BASE                   "$ENTITY_BASE/../interrupt_manager"
set MI_SPLIT_BASE             "$OFM_PATH/comp/mi_tools/splitter"
set MI32_ASYNC_HANDSHAKE_BASE "$OFM_PATH/comp/mi_tools/async"

if { $ARCHGRP == "FULL" } {
    set MOD "$MOD $ENTITY_BASE/sysmon_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/sysmon_virtex5.vhd"
    set MOD "$MOD $ENTITY_BASE/id_comp.vhd"
    set MOD "$MOD $ENTITY_BASE/id_top_virtex5.vhd"
    set COMPONENTS [list \
                        [list "INTERRUPT_MANAGER" $IM_BASE "FULL"] \
                   ]
}

if { $ARCHGRP == "VIRTEX6" } {
    set MOD "$MOD $ENTITY_BASE/sysmon_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/sysmon_virtex6.vhd"
    set MOD "$MOD $ENTITY_BASE/id_comp.vhd"
    set MOD "$MOD $ENTITY_BASE/id_top_virtex6.vhd"
    set COMPONENTS [list \
                        [list "INTERRUPT_MANAGER"    $IM_BASE                   "FULL"] \
                        [list "MI_SPLITTER"          $MI_SPLIT_BASE             "FULL"] \
                        [list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL"] \
                   ]
}

if { $ARCHGRP == "VIRTEX7" } {
    set MOD "$MOD $ENTITY_BASE/sysmon_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/sysmon_virtex7.vhd"
    set MOD "$MOD $ENTITY_BASE/id_comp.vhd"
    set MOD "$MOD $ENTITY_BASE/id_top_virtex7.vhd"
    set COMPONENTS [list \
                        [list "INTERRUPT_MANAGER" $IM_BASE "FULL"] \
                   ]
}

if { $ARCHGRP == "USP" } {
    set MOD "$MOD $ENTITY_BASE/sysmon_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/sysmon_usp.vhd"
    set MOD "$MOD $ENTITY_BASE/id_comp.vhd"
    set MOD "$MOD $ENTITY_BASE/id_top_virtex7.vhd"
    set COMPONENTS [list \
                        [list "INTERRUPT_MANAGER" $IM_BASE "FULL"] \
                   ]
}


if { $ARCHGRP == "DOC" } {
    set MOD "$MOD $ENTITY_BASE/sysmon_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/sysmon_virtex5.vhd"
    set MOD "$MOD $ENTITY_BASE/sysmon_virtex6.vhd"
    set MOD "$MOD $ENTITY_BASE/sysmon_virtex7.vhd"
    set MOD "$MOD $ENTITY_BASE/id_comp.vhd"
    set MOD "$MOD $ENTITY_BASE/id_top_virtex5.vhd"
    set MOD "$MOD $ENTITY_BASE/id_top_virtex6.vhd"
    set MOD "$MOD $ENTITY_BASE/id_top_virtex7.vhd"
    set COMPONENTS [list \
                        [list "INTERRUPT_MANAGER"    $IM_BASE                   "FULL"] \
                        [list "MI_SPLITTER"          $MI_SPLIT_BASE             "FULL"] \
                        [list "MI32_ASYNC_HANDSHAKE" $MI32_ASYNC_HANDSHAKE_BASE "FULL"] \
                   ]
}

set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
