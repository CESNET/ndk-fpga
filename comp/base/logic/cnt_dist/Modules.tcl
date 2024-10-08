# Modules.tcl: Local include tcl script
# Copyright (C) 2005 CESNET
# Author: Martin Mikusek <martin.mikusek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause
#

set DP_DISTMEM_BASE "$ENTITY_BASE/../../mem/gen_lutram/compatibility"

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   # List of components
   set COMPONENTS [list \
                        [list "DP_DISTMEM" $DP_DISTMEM_BASE "FULL"]  \
                  ]

   set MOD "$MOD $ENTITY_BASE/cnt_dist.vhd"
}

# Source file for empty component - empty architecture
if { $ARCHGRP == "EMPTY" } {
}

# debug component
if { $ARCHGRP == "DEBUG" } {
}
