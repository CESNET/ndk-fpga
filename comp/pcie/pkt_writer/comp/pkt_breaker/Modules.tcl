# Modules.tcl: Modules of the component
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"
set MFB_LOGIC_BASE      "$OFM_PATH/comp/mfb_tools/logic"
set MFB_AXI_BASE        "$OFM_PATH/comp/mfb_tools/axi"
set AXIS_FLOW_BASE      "$OFM_PATH/comp/axis_tools/flow"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"

# Components
lappend COMPONENTS [ list "OFFSET_REACHED"     "$MFB_LOGIC_BASE/offset_reached"    "FULL" ]
lappend COMPONENTS [ list "MFB2AXI"            "$MFB_AXI_BASE/mfb2axi"             "FULL" ]
lappend COMPONENTS [ list "AXI2MFB"            "$MFB_AXI_BASE/axi2mfb"             "FULL" ]
lappend COMPONENTS [ list "FRAME_FRACTURER"    "$AXIS_FLOW_BASE/frame_fracturer"   "FULL" ]

# Modules
lappend MOD "$ENTITY_BASE/ppw_pkt_breaker.vhd"
