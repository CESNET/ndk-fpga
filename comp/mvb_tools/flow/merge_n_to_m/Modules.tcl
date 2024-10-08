# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET z. s. p. o.
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
set MUX_BASE   "$OFM_PATH/comp/base/logic/mux"
set N_ONE_BASE "$OFM_PATH/comp/base/logic/n_one"
set PKG_BASE   "$OFM_PATH/comp/base/pkg"
set PIPE_BASE  "$OFM_PATH/comp/base/misc/pipe"

lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

lappend COMPONENTS [ list "GEN_MUX"  $MUX_BASE    "FULL" ]
lappend COMPONENTS [ list "N_ONE"    $N_ONE_BASE  "FULL" ]
lappend COMPONENTS [ list "PIPE"     $PIPE_BASE   "FULL" ]

set MOD "$MOD $ENTITY_BASE/merge_n_to_m_ent.vhd"
set MOD "$MOD $ENTITY_BASE/merge_n_to_m.vhd"
set MOD "$MOD $ENTITY_BASE/shakedown.vhd"
