# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set GEN_NOR_BASE "$OFM_PATH/comp/base/logic/gen_nor"

set COMPONENTS [ list \
   [ list "GEN_NOR" $GEN_NOR_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/enc_logic.vhd"
set MOD "$MOD $ENTITY_BASE/enc_ent.vhd"
set MOD "$MOD $ENTITY_BASE/enc.vhd"
