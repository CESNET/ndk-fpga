# Modules.tcl: Components include script
# Copyright (C) 2024 BrnoLogic, Ltd.
# Author(s): Radek Hajek <hajek@brnologic.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set SV_COMP_BASE  "$ENTITY_BASE/../../"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [list "AXI_PIPE" $SV_COMP_BASE/axi/axi_pipe "FULL" ]
lappend COMPONENTS [list "MFB_PIPE" $SV_COMP_BASE/flow/pipe "FULL" ]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/axi2mfb.vhd"
