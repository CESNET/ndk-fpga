# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET z. s. p. o.
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
set MUX_BASE   "$OFM_PATH/comp/base/logic/mux"
set N_ONE_BASE "$OFM_PATH/comp/base/logic/n_one"
set PKG_BASE   "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [ list \
   [ list "GEN_MUX"  $MUX_BASE    "FULL" ] \
   [ list "N_ONE"    $N_ONE_BASE  "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/merge_n_to_m_rotate_ent.vhd"
set MOD "$MOD $ENTITY_BASE/merge_n_to_m_rotate.vhd"
set MOD "$MOD $ENTITY_BASE/shakedown_rotate.vhd"
