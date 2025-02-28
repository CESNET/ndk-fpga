# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set FIFOXM_BASE      "$OFM_PATH/comp/base/fifo/fifox_multi"
set LOGIC_BASE       "$OFM_PATH/comp/base/logic"
set MFB_BASE         "$OFM_PATH/comp/mfb_tools"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "FIFOX_MULTI"          $FIFOXM_BASE                      "FULL" ]
lappend COMPONENTS [ list "ONES_INSERTOR"        "$LOGIC_BASE/ones_insertor"       "FULL" ]
lappend COMPONENTS [ list "BARREL_SHIFTER"       "$LOGIC_BASE/barrel_shifter"      "FULL" ]
lappend COMPONENTS [ list "MFB_FRAME_LNG"        "$MFB_BASE/logic/frame_lng"       "FULL" ]
lappend COMPONENTS [ list "MFB_FRAME_EXTENDER"   "$MFB_BASE/edit/frame_extender"   "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mfb_mvb_prepender.vhd"

