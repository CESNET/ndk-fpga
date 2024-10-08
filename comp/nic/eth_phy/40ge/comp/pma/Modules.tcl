# Modules.tcl:
# Copyright (C) 2013 CESNET
# Author(s): Stepan Friedl <friedl@cesnet.cz>, Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set OPEN_LOOP_BASE "$OFM_PATH/comp/base/async/open_loop"
set ARESET_BASE    "$OFM_PATH/comp/base/async/reset"
set BLK_LOCK_BASE  "$OFM_PATH/comp/nic/eth_phy/comp/blklock"

lappend COMPONENTS [ list "ASYNC_OPEN_LOOP" $OPEN_LOOP_BASE "FULL" ]
lappend COMPONENTS [ list "ASYNC_RESET"     $ARESET_BASE    "FULL" ]
lappend COMPONENTS [ list "BLOCK LOCK"      $BLK_LOCK_BASE  "FULL" ]

lappend MOD "$ENTITY_BASE/gt_init.vhd"

# Top level
lappend MOD "$ENTITY_BASE/pma_xlaui_gty.vhd"
