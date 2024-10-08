# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set TCAM_BASE          "$OFM_PATH/comp/base/mem/tcam2"
set DEC1FN2B_BASE      "$OFM_PATH/comp/base/logic/dec1fn"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "TCAM2"           $TCAM_BASE       "FULL" ] \
   [list "DEC1FN2B"        $DEC1FN2B_BASE   "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/get_mac.vhd"
set MOD "$MOD $ENTITY_BASE/mac_check.vhd"
