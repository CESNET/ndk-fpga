# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SUM_ONE_BASE "$OFM_PATH/comp/base/logic/sum_one"

# Set components
lappend COMPONENTS [ list "SUM_ONE" $SUM_ONE_BASE "FULL" ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_speed_meter.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_speed_meter_mi.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
