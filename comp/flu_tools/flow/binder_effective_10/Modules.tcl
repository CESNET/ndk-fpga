# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Tomas Zavodnik <zavodnik@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"

# FLU binder
set BINDER_EFF_BASE     "$FLU_BASE/flow/binder_effective"

set COMPONENTS [list \
      [list "BINDER_EFF"     $BINDER_EFF_BASE     "FULL" ] \
]

# FLU Binder 10
set MOD "$MOD $ENTITY_BASE/hdr_insert.vhd"
set MOD "$MOD $ENTITY_BASE/binder10_ent.vhd"
set MOD "$MOD $ENTITY_BASE/binder10_arch.vhd"
