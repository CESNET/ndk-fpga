# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE   "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE "$OFM_PATH/comp/base/logic"
set MFB_BASE   "$OFM_PATH/comp/mfb_tools"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [list "SUM_ONE" "$LOGIC_BASE/sum_one"               "FULL"] \
   [list "DEC1FN"  "$LOGIC_BASE/enc"                   "FULL"] \
   [list "GEN_MUX" "$LOGIC_BASE/mux"                   "FULL"] \
   [list "MFB_AUX" "$MFB_BASE/logic/auxiliary_signals" "FULL"] \
   [list "MFB_AUX" "$MFB_BASE/logic/frame_lng_check"   "FULL"] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mac_seg.vhd"
