# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set OPEN_LOOP_BASE "$ENTITY_BASE/../open_loop"

set COMPONENTS [ list [ list "ASYNC_OPEN_LOOP" $OPEN_LOOP_BASE "FULL" ] ]

set MOD "$MOD $ENTITY_BASE/general_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/general.vhd"
