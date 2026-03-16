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
lappend COMPONENTS [ list "BARREL_SHIFTER_GEN" $BARREL_SHIFTER_BASE "FULL" ]
lappend COMPONENTS [ list "MERGE_N_TO_M"       $MERGE_N_TO_M_BASE   "FULL" ]
lappend COMPONENTS [ list "SHAKEDOWN"          $SHAKEDOWN_BASE      "FULL" ]
lappend COMPONENTS [ list "FIFOX_BASE"         $FIFOX_BASE          "FULL" ]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/fifox_multi_ent.vhd"
set MOD "$MOD $ENTITY_BASE/fifox_multi_shakedown.vhd"
set MOD "$MOD $ENTITY_BASE/fifox_multi_full.vhd"
