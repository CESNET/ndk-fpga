# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set BIN2HOT_BASE "$OFM_PATH/comp/base/logic/bin2hot"
set DEC1FN2B_BASE "$OFM_PATH/comp/base/logic/dec1fn"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
    [ list "BIN2HOT"  $BIN2HOT_BASE  "FULL" ] \
    [ list "DEC1FN2B" $DEC1FN2B_BASE "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_cutter_simple.vhd"
