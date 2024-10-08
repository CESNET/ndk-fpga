# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2008 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#         Petr Kastovsky <xkasto01@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set SV_COMMON_BASE   "$OFM_PATH/comp/ver"

set COMPONENTS [list \
	[ list "SV_COMMON"   $SV_COMMON_BASE    "FULL"] \
]
if { $ARCHGRP == "FULL" } {
	set MOD "$MOD $ENTITY_BASE/sv_mi32_pkg.sv"
} elseif { $ARCHGRP == "SLAVE" } {
	set MOD "$MOD $ENTITY_BASE/sv_mi32slave_pkg.sv"
} elseif { $ARCHGRP == "UNIFIED" } {
	set MOD "$MOD $ENTITY_BASE/sv_mi_pkg.sv"
}
