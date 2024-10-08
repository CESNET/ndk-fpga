# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/binder_ent.vhd"
set MOD "$MOD $ENTITY_BASE/binder_stupid.vhd"
set MOD "$MOD $ENTITY_BASE/binder_2to1.vhd"
set MOD "$MOD $ENTITY_BASE/binder_plus_ent.vhd"
set MOD "$MOD $ENTITY_BASE/binder_plus_stupid.vhd"
set MOD "$MOD $ENTITY_BASE/binder_plus_2to1.vhd"
set MOD "$MOD $ENTITY_BASE/binder_plus_3to1.vhd"

set COMPONENTS [list [list "FLU_MULTIPLEXER"        "$FLU_BASE/flow/multiplexer"       "FULL"]]
