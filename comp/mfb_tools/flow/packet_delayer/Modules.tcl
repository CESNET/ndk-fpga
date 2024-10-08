# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set MFB_FIFOX_BASE           "$OFM_PATH/comp/mfb_tools/storage/fifox"
set MFB_FRAME_MASKER_BASE    "$OFM_PATH/comp/mfb_tools/flow/frame_masker"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "MFB_FIFOX"         $MFB_FIFOX_BASE         "FULL" ]
lappend COMPONENTS [ list "MFB_FRAME_MASKER"  $MFB_FRAME_MASKER_BASE  "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mfb_packet_delayer.vhd"

