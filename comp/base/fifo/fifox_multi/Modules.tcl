# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set BARREL_SHIFTER_BASE "$OFM_PATH/comp/base/logic/barrel_shifter"
set MERGE_N_TO_M_BASE   "$OFM_PATH/comp/mvb_tools/flow/merge_n_to_m"
set SHAKEDOWN_BASE      "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set FIFOX_BASE          "$OFM_PATH/comp/base/fifo/fifox"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
    [ list "BARREL_SHIFTER_GEN" $BARREL_SHIFTER_BASE "FULL" ] \
    [ list "MERGE_N_TO_M"       $MERGE_N_TO_M_BASE   "FULL" ] \
    [ list "SHAKEDOWN"          $SHAKEDOWN_BASE      "FULL" ] \
    [ list "FIFOX_BASE"         $FIFOX_BASE          "FULL" ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/fifox_multi_ent.vhd"
set MOD "$MOD $ENTITY_BASE/fifox_multi_shakedown.vhd"
#######
# !!! MUST BE INCLUDED LAST TO BECOME THE DEFAULT ARCHITECTURE !!!
set MOD "$MOD $ENTITY_BASE/fifox_multi_full.vhd"
#######
