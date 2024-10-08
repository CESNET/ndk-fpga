# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author(s): Pavel Benáček <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
global SIMULATION

set BMEM_BASE     "$OFM_PATH/comp/base/mem/dp_bmem"

# Set packages
set PACKAGES      "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES      "$PACKAGES $ENTITY_BASE/dp_bmem_V7_func.vhd"
set PACKAGES      "$PACKAGES $ENTITY_BASE/sdp_bmem_V7_func.vhd"

set MOD           "$MOD $ENTITY_BASE/dp_bmem_V7_ent.vhd"
set MOD           "$MOD $ENTITY_BASE/sdp_bmem_V7_ent.vhd"

# Extra simulation source files (DISABLED)
if {false && [info exists SIMULATION] && $SIMULATION} then {
   set MOD "$MOD $ENTITY_BASE/dp_bmem_V7_behav.vhd"

   # Set components
   set COMPONENTS [list \
      [ list "BMEM"     $BMEM_BASE     "FULL" ] \
   ]

# Synthetise source files
} else {
   set MOD "$MOD $ENTITY_BASE/dp_bmem_V7_arch.vhd"
   set MOD "$MOD $ENTITY_BASE/sdp_bmem_V7_arch.vhd"
}
