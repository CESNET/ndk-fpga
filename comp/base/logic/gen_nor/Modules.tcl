# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/gen_nor_ent.vhd"
set MOD "$MOD $ENTITY_BASE/gen_nor.vhd"

set CARRY_CHAIN_BASE    "$OFM_PATH/comp/base/logic/carry_chain"
set GEN_NOR_FIXED_BASE    "$OFM_PATH/comp/base/logic/gen_nor/comp/gen_nor_fixed"
set GEN_AND_FIXED_BASE    "$OFM_PATH/comp/base/logic/gen_nor/comp/gen_and_fixed"

set COMPONENTS [ list \
                  [ list "CARRY_CHAIN"                 $CARRY_CHAIN_BASE                 "FULL" ] \
                  [ list "GEN_NOR_FIXED"                 $GEN_NOR_FIXED_BASE                 "FULL" ] \
                  [ list "GEN_AND_FIXED"                 $GEN_AND_FIXED_BASE                 "FULL" ] \
               ]
