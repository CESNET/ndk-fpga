# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set ASYNC_RESET_BASE "$OFM_PATH/comp/base/async/reset"
set OPEN_LOOP_BASE   "$OFM_PATH/comp/base/async/open_loop"
set MI_ASYNC_BASE    "$OFM_PATH/comp/mi_tools/async"

# Components
lappend COMPONENTS [list "ASYNC_RESET"     $ASYNC_RESET_BASE "FULL"]
lappend COMPONENTS [list "ASYNC_OPEN_LOOP" $OPEN_LOOP_BASE   "FULL"]
lappend COMPONENTS [list "MI_ASYNC"        $MI_ASYNC_BASE    "FULL"]

# Source files
lappend MOD "$ENTITY_BASE/pulse_extend.vhd"
lappend MOD "$ENTITY_BASE/mgmt.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"
