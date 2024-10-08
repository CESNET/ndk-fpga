# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2022 CESNET
# Author: David Beneš <benes.david2000@seznam.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set OPEN_LOOP_BASE "$OFM_PATH/comp/base/async/open_loop"
# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [list "open_loop"  $OPEN_LOOP_BASE  "FULL"]


# Files
lappend MOD "$ENTITY_BASE/axi4_lite_mi_bridge.vhd"

