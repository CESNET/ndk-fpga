# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$ENTITY_BASE/reset.vhd"

lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/async_reset.xdc SCOPED_TO_REF ASYNC_RESET]
lappend SRCS(CONSTR_QUARTUS) [list "$ENTITY_BASE/async_reset.sdc" SDC_ENTITY_FILE ASYNC_RESET]
