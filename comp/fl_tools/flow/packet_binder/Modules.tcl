# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Michal Spacek <xspace14@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# Set paths

set FL_BASE       "$ENTITY_BASE/../.."
set FIFO_BASE     "$FL_BASE/storage/fifo"

# Full FrameLink packet binder
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/packet_binder.vhd"
}
# components
set COMPONENTS [list \
   [ list "PKG_MATH"    $OFM_PATH/comp/base/pkg  "MATH"] \
   [ list "FIFO"        $FIFO_BASE           "FULL"] \
]


# covers
set MOD "$MOD $ENTITY_BASE/top/packet_binder_fl16.vhd"
set MOD "$MOD $ENTITY_BASE/top/packet_binder_fl32.vhd"
