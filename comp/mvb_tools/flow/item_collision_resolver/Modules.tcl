# Modules.tcl: Script to compile single module
# Copyright (C) 2024 CESNET
# Author: Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFO_BASE  "$OFM_PATH/comp/base/fifo"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "FIFOX_MULTI"  "$FIFO_BASE/fifox_multi"  "FULL" ]

lappend MOD "$ENTITY_BASE/mvb_item_collision_resolver.vhd"
