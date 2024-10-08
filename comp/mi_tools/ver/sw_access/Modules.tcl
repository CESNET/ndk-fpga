# Modules.tcl: Modules.tcl script to compile the design
# Copyright (C) 2015 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

global LIBCOMMLBR_INCLUDE

set COMPONENTS [ list [list "MI32_VER"  "$ENTITY_BASE/.."   "FULL"] ]

if {$ARCHGRP == "NFB_IFC"} {
    set MOD    "$MOD $ENTITY_BASE/dpi_sw_access_ifc.sv"
    set SV_LIB "[list [list $ENTITY_BASE/dpi_sw_access MAKE_PARAMS "EXTRA_CFLAGS=NFB_IFC"]] $SV_LIB"
} else {
    set MOD    "$MOD $ENTITY_BASE/dpi_sw_access.sv"
    set SV_LIB "$ENTITY_BASE/dpi_sw_access $SV_LIB"
}

if { $ARCHGRP == "COMBO" } {
    set SV_LIB "$ENTITY_BASE/combo/combo $SV_LIB"
    set SV_LIB "$LIBCOMMLBR_INCLUDE/commlbr $SV_LIB"
}

if { $ARCHGRP == "NFB" } {
    set SV_LIB "$ENTITY_BASE/nfb/nfb $SV_LIB"
}
