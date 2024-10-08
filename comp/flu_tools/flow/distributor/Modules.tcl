# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/distributor_ent.vhd"
set MOD "$MOD $ENTITY_BASE/distributor.vhd"

set MOD "$MOD $ENTITY_BASE/distributor_1to2.vhd"
set MOD "$MOD $ENTITY_BASE/distributor_1to3.vhd"
set MOD "$MOD $ENTITY_BASE/distributor_1to4.vhd"

set MOD "$MOD $ENTITY_BASE/distributor_1to2_fork.vhd"
