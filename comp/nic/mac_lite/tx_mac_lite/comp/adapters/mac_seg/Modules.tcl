# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE   "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE "$OFM_PATH/comp/base/logic"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "DEC1FN"  "$LOGIC_BASE/dec1fn"                           "FULL"] \
   [list "MFB_AUX" "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals" "FULL"] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mac_seg.vhd"
