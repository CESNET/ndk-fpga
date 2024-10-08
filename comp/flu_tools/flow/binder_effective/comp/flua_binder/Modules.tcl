# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"
set FLU_PIPE_BASE       "$FLU_BASE/flow/pipe"

# Packages base
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# Component list
set COMPONENTS [list \
         [list "FLU_PIPE"     $FLU_PIPE_BASE       "FULL"   ] \
]

# Other FLUA Binder components
set MOD "$MOD $ENTITY_BASE/flua_shifter_core.vhd"
set MOD "$MOD $ENTITY_BASE/flua_shifter.vhd"
set MOD "$MOD $ENTITY_BASE/flua_binder_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/flua_binder_gap_fsm.vhd"

# FLUA Binder entity and architecture
set MOD "$MOD $ENTITY_BASE/flua_binder_ent.vhd"
set MOD "$MOD $ENTITY_BASE/flua_binder_arch.vhd"
