# Modules.tcl: Components include script
# Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
# Author(s): Radek Hajek <hajek@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set AXIS_PIPE_BASE   "$OFM_PATH/comp/axis_tools/flow/pipe"
set MFB_PIPE_BASE    "$OFM_PATH/comp/mfb_tools/flow/pipe"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [list "AXIS_PIPE" $AXIS_PIPE_BASE "FULL" ]
lappend COMPONENTS [list "MFB_PIPE"  $MFB_PIPE_BASE  "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mfb2axi.vhd"
