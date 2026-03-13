# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE          "$OFM_PATH/comp/base/logic"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Components
lappend COMPONENTS [ list "LAST_ONE"           "$LOGIC_BASE/last_one"       "FULL" ]
lappend COMPONENTS [ list "BARREL_SHIFTER_GEN" "$LOGIC_BASE/barrel_shifter" "FULL" ]
lappend COMPONENTS [ list "GEN_ENC"            "$LOGIC_BASE/enc"            "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/axis_packet_concatenator.vhd"
