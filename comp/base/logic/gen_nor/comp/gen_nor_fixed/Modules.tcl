# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/gen_nor_fixed_ent.vhd"
set MOD "$MOD $ENTITY_BASE/gen_nor_fixed.vhd"

set CARRY_CHAIN_BASE    "$OFM_PATH/comp/base/logic/carry_chain"

set COMPONENTS [ list \
                  [ list "CARRY_CHAIN"                 $CARRY_CHAIN_BASE                 "FULL" ] \
               ]
