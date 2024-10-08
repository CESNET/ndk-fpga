# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET
# Author: Stepan Friedl <friedl@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MOD "$MOD $ENTITY_BASE/width_conv_1to4.vhd"
set MOD "$MOD $ENTITY_BASE/width_conv_4to1.vhd"

lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/width_conv_1to4.xdc SCOPED_TO_REF width_conv_1to4]
lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/width_conv_4to1.xdc SCOPED_TO_REF width_conv_4to1]
# TBD:
#lappend SRCS(CONSTR_QUARTUS) [list $ENTITY_BASE/open_loop.sdc SDC_ENTITY_FILE ASYNC_OPEN_LOOP]
