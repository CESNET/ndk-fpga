# Modules.tcl: Modules of the component
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE          "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE        "$OFM_PATH/comp/base/logic"
set AXIS_BASE         "$ENTITY_BASE/../.."

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Components
lappend COMPONENTS [ list "LAST_ONE"         "$LOGIC_BASE/last_one"          "FULL" ]
lappend COMPONENTS [ list "ENCODER"          "$LOGIC_BASE/enc"               "FULL" ]
lappend COMPONENTS [ list "BARREL_SHIFTER"   "$LOGIC_BASE/barrel_shifter"    "FULL" ]
lappend COMPONENTS [ list "AXIS_FIFO"        "$AXIS_BASE/storage/fifo"       "FULL" ]

# Modules
lappend MOD "$ENTITY_BASE/axis_frame_fracturer.vhd"
