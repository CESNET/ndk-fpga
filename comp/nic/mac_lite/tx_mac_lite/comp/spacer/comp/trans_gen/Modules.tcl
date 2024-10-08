# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE           "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set MVB_SHAKEDOWN_BASE    "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set SHAKEDOWN_BASE        "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"

set COMPONENTS [list \
    [list "MVB_SHAKEDOWN"  $MVB_SHAKEDOWN_BASE     "FULL" ] \
    [list "SHAKEDOWN"      $SHAKEDOWN_BASE         "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/trans_gen.vhd"
