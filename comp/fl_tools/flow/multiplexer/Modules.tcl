#
# Modules.tcl: Components include script
# Copyright (C) 2008 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set DEC1FN_BASE $OFM_PATH/comp/base/logic/dec1fn
set MUX_BASE $OFM_PATH/comp/base/logic/mux
set SHIFTER_BASE $OFM_PATH/comp/base/logic/barrel_shifter
set FIRSTONE_BASE $OFM_PATH/comp/base/misc/first_one_detector

set COMPONENTS [list \
    [list "DEC1FN"     $DEC1FN_BASE      "FULL"] \
    [list "MUX"        $MUX_BASE         "FULL"] \
    [list "SHIFTER"    $SHIFTER_BASE     "FULL"] \
    [list "FIRSTONE"   $FIRSTONE_BASE    "FULL"] \
]

# packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set MOD "$MOD $ENTITY_BASE/multiplexer.vhd"
