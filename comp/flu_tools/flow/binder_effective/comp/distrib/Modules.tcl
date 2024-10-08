# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set COMPONENTS [list  [list "FLU_DISTRIBUTOR"    "$FLU_BASE/flow/distributor"       "FULL" ] ]

set MOD "$MOD $ENTITY_BASE/distrib_ent.vhd"
set MOD "$MOD $ENTITY_BASE/distrib_arch.vhd"
