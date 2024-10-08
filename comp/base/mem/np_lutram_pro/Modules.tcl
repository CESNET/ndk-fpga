# Modules.tcl: Components include script
# Copyright (C) 2016 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MOD "$MOD $ENTITY_BASE/np_lutram_pro.vhd"

set NP_LUTRAM_FIXED_BASE "$ENTITY_BASE/comp/np_lutram_fixed"
set GEN_MUX_BASE         "$OFM_PATH/comp/base/logic/mux"
set BIN2HOT_BASE         "$OFM_PATH/comp/base/logic/bin2hot"
set GEN_ENC_BASE         "$OFM_PATH/comp/base/logic/enc"

set COMPONENTS [ list \
    [ list "MATH_PACK"               "$OFM_PATH/comp/base/pkg"               "MATH" ] \
    [ list "TYPE_PACK"               "$OFM_PATH/comp/base/pkg"               "TYPE" ] \
    [ list "np_lutram_fixed"         "$NP_LUTRAM_FIXED_BASE"                "FULL" ] \
    [ list "gen_mux"                 "$GEN_MUX_BASE"                        "FULL" ] \
    [ list "BIN2HOT"                 "$BIN2HOT_BASE"                        "FULL" ] \
    [ list "GEN_ENC"                 "$GEN_ENC_BASE"                        "FULL" ] \
]
