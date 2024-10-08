# Modules.tcl: Component include tcl script.
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FL_PIPE_BASE   "$OFM_PATH/comp/fl_tools/flow/pipe"
set FLU_PIPE_BASE   "$ENTITY_BASE/../../../flu_tools/flow/pipe"

set COMPONENTS [list \
    [list "FL_PIPE"    $FL_PIPE_BASE     "FULL"] \
    [list "FLU_PIPE"   $FLU_PIPE_BASE    "FULL"] \
    [list "MATH_PACK"  "$ENTITY_BASE/../../../base/pkg/" "MATH"] \
]

# set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
set MOD "$ENTITY_BASE/flu2fl_ent.vhd\
         $ENTITY_BASE/flu2fl_top.vhd"
