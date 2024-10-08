# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE         "$OFM_PATH/comp/base/logic"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "GEN_ENC"     "$LOGIC_BASE/enc"        "FULL"] \
   [list "FIRST_ONE"   "$LOGIC_BASE/first_one"  "FULL"] \
   [list "LAST_ONE"    "$LOGIC_BASE/last_one"   "FULL"] \
   [list "AFTER_ONE"   "$LOGIC_BASE/after_one"  "FULL"] \
   [list "BEFORE_ONE"  "$LOGIC_BASE/before_one" "FULL"] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/xgmii_align.vhd"
set MOD "$MOD $ENTITY_BASE/umii_ctrl_dec.vhd"
set MOD "$MOD $ENTITY_BASE/umii_dec_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/umii_dec.vhd"
