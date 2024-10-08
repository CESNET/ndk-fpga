# Modules.tcl: Components include script
# Copyright (C) 2014 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set COMPONENTS [list \
    [list "SLR_CROSSING"    "$OFM_PATH/comp/base/misc/slr_crossing"     "FULL"] \
]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/comp/mi_slr_crossing_src.vhd"
set MOD "$MOD $ENTITY_BASE/comp/mi_slr_crossing_dst.vhd"
set MOD "$MOD $ENTITY_BASE/mi_slr_crossing.vhd"
