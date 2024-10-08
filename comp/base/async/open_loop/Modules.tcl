# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set MOD "$ENTITY_BASE/open_loop.vhd"


lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/open_loop.xdc SCOPED_TO_REF ASYNC_OPEN_LOOP]
lappend SRCS(CONSTR_QUARTUS) [list $ENTITY_BASE/open_loop.sdc SDC_ENTITY_FILE ASYNC_OPEN_LOOP]
