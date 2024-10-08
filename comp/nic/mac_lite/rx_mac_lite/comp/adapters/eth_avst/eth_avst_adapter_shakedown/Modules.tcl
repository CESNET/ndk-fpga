# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set FIFOX_MULTI_BASE    "$OFM_PATH/comp/base/fifo/fifox_multi"
set BARREL_SHIFTER_BASE "$OFM_PATH/comp/base/logic/barrel_shifter"
set SUM_ONE_BASE        "$OFM_PATH/comp/base/logic/sum_one"
set PKG_BASE            "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
    [ list "FIFOX_MULTI"        $FIFOX_MULTI_BASE    "FULL" ] \
    [ list "BARREL_SHIFTER_GEN" $BARREL_SHIFTER_BASE "FULL" ] \
    [ list "SUM_ONE"            $SUM_ONE_BASE        "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/compressor_lite.vhd"
set MOD "$MOD $ENTITY_BASE/eth_avst_adapter_shakedown.vhd"
