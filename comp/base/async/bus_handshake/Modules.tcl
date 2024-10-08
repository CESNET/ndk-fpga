# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set OPEN_LOOP_BASE "$ENTITY_BASE/../open_loop"

set COMPONENTS [ list [ list "ASYNC_OPEN_LOOP" $OPEN_LOOP_BASE "FULL" ] ]

set MOD "$MOD $ENTITY_BASE/bus_handshake_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/sync_pgen.vhd"
set MOD "$MOD $ENTITY_BASE/bus_handshake.vhd"

lappend SRCS(CONSTR_VIVADO) [list "$ENTITY_BASE/bus_handshake.xdc" SCOPED_TO_REF ASYNC_BUS_HANDSHAKE PROCESSING_ORDER LATE]
lappend SRCS(CONSTR_QUARTUS) [list "$ENTITY_BASE/bus_handshake.sdc" SDC_ENTITY_FILE ASYNC_BUS_HANDSHAKE]
