# Modules.tcl: Local include tcl script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author: Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_COMMON_BASE "$OFM_PATH/comp/ver"
set SV_MVB_BASE    "$OFM_PATH/comp/mvb_tools/ver"

lappend COMPONENTS [ list "SV_COMMON" $SV_COMMON_BASE "FULL" ]
lappend COMPONENTS [ list "SV_MVB"    $SV_MVB_BASE    "FULL" ]

lappend MOD "$ENTITY_BASE/sv_rb_pkg.sv"
