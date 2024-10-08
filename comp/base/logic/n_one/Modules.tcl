# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MATH_PKG "$OFM_PATH/comp/base/pkg"
set MUX_BASE "$OFM_PATH/comp/base/logic/mux"

set PACKAGES "$PACKAGES $MATH_PKG/math_pack.vhd"
set PACKAGES "$PACKAGES $MATH_PKG/type_pack.vhd"

set COMPONENTS [ list \
   [ list "GEN_MUX" $MUX_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/n_one_ent.vhd"
set MOD "$MOD $ENTITY_BASE/n_one_core.vhd"
set MOD "$MOD $ENTITY_BASE/n_one_logic.vhd"
set MOD "$MOD $ENTITY_BASE/n_one.vhd"
