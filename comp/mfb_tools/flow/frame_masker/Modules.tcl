# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MFB_PIPE_BASE   "$OFM_PATH/comp/mfb_tools/flow/pipe"
set LAST_VLD_BASE   "$OFM_PATH/comp/mvb_tools/aggregate/last_vld"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "MFB_PIPE"      $MFB_PIPE_BASE      "FULL" ]
lappend COMPONENTS [ list "MVB_LAST_VLD"  $LAST_VLD_BASE      "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mfb_frame_masker.vhd"

