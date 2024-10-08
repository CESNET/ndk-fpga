# Modules.tcl: script to compile single module
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_COMMON_BASE "$OFM_PATH/comp/ver"
set SV_FLU_BASE    "$OFM_PATH/comp/flu_tools/ver"
set SV_AXI_BASE    "$OFM_PATH/comp/ver/axi"
set SV_MI_BASE     "$OFM_PATH/comp/mi_tools/ver"

set COMPONENTS [list \
    [list "SV_COMMON" $SV_COMMON_BASE "FULL"] \
    [list "SV_FLU"    $SV_FLU_BASE    "FULL"] \
    [list "SV_AXI"    $SV_AXI_BASE    "FULL"] \
    [list "SV_MI"     $SV_MI_BASE     "FULL"] \
]

lappend MOD "$ENTITY_BASE/sv_ndp_software_pkg.sv"
