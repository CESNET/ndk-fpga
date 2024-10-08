# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# packages:
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# basic logic components:
set LOGIC_BASE    "$OFM_PATH/comp/base/logic"
set MOD "$MOD $LOGIC_BASE/dec1fn/dec1fn_enable.vhd"
set MOD "$MOD $LOGIC_BASE/dec1fn/dec1fn.vhd"
set MOD "$MOD $LOGIC_BASE/enc/enc.vhd"
set MOD "$MOD $LOGIC_BASE/or/or.vhd"

# modules:
set MOD "$MOD $ENTITY_BASE/transformer_plus_up.vhd"
set MOD "$MOD $ENTITY_BASE/transformer_plus_down.vhd"
set MOD "$MOD $ENTITY_BASE/transformer_plus_ent.vhd"
set MOD "$MOD $ENTITY_BASE/transformer_plus.vhd"

# components:
set COMPONENTS [list\
  [list "DYNAMIC_SHREG" "$OFM_PATH/comp/base/shreg/sh_reg_base"   "FULL"]\
  [list "SIPO_SHREG"    "$OFM_PATH/comp/base/shreg/sipo"          "FULL"]\
  [list "SIPO_SHREG"    "$OFM_PATH/comp/base/logic/mux"           "FULL"]\
]
