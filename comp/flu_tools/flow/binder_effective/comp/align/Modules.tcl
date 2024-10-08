# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"

set FLU2FL_BASE         "$FLU_BASE/fl/flu2fl"

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/align_ent.vhd"
set MOD "$MOD $ENTITY_BASE/align_arch.vhd"

set COMPONENTS [list \
         [list "FLU2FL"    $FLU2FL_BASE      "FULL"   ] \
]
