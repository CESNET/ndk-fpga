# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
set MUX      "$OFM_PATH/comp/base/logic/mux"
set MI_PIPE  "$ENTITY_BASE/../pipe"

set COMPONENTS [list \
    [list "GEN_MUX_ONEHOT"       $MUX      "FULL"] \
    [list "MI_PIPE"     $MI_PIPE    "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/reg_type.vhd"
set MOD "$MOD $ENTITY_BASE/be_reg.vhd"
set MOD "$MOD $ENTITY_BASE/mi_reg.vhd"
set MOD "$MOD $ENTITY_BASE/MI_register_array.vhd"
set MOD "$MOD $ENTITY_BASE/synth/MI_register_array_top.vhd"
