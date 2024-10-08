# Modules.tcl: Local include tcl script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components
set MOD "$ENTITY_BASE/open_loop_smd.vhd"

lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/open_loop_smd.xdc SCOPED_TO_REF ASYNC_OPEN_LOOP_SMD PROCESSING_ORDER LATE]
lappend SRCS(CONSTR_QUARTUS) [list $ENTITY_BASE/open_loop_smd.sdc SDC_ENTITY_FILE ASYNC_OPEN_LOOP_SMD]
