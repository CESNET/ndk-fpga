# Modules.tcl: Components include script
# Copyright (C) 2016 CESNET z. s. p. o.
# Author(s): Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set MATH_PKG  "$OFM_PATH/comp/base/pkg"

set MOD "$MOD $ENTITY_BASE/item_trans_ctrl.vhd"
set GEN_ENC_BASE "$OFM_PATH/comp/base/logic/enc"
set DEC1FN_BASE "$OFM_PATH/comp/base/logic/dec1fn"
set GEN_MUX_BASE "$OFM_PATH/comp/base/logic/mux"

set COMPONENTS [list \
   [ list "GEN_MUX_ONEHOT"                 $GEN_MUX_BASE                 "full" ] \
   [ list "GEN_ENC"                 $GEN_ENC_BASE                 "full" ] \
   [ list "DEC1FN_ENABLE"           $DEC1FN_BASE                 "full" ] \
]

set PACKAGES "$PACKAGES $MATH_PKG/math_pack.vhd"
