# Modules.tcl: Modules.tcl script to compile all design
# Copyright (C) 2014 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set COMPONENTS [list \
    [list "SH_REG_BASE"    "$OFM_PATH/comp/base/shreg/sh_reg_base"      "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/comp/slr_crossing_src.vhd"
set MOD "$MOD $ENTITY_BASE/comp/slr_crossing_dst.vhd"
set MOD "$MOD $ENTITY_BASE/slr_crossing.vhd"
set MOD "$MOD $ENTITY_BASE/comp/slr_crossing_data_only_src.vhd"
set MOD "$MOD $ENTITY_BASE/comp/slr_crossing_data_only_dst.vhd"
set MOD "$MOD $ENTITY_BASE/slr_crossing_data_only.vhd"
