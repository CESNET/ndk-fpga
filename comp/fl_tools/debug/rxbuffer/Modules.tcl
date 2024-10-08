# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Libor Polcak <xpolca03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set FL_BASE       "$ENTITY_BASE/../.."
set FIFO_BASE     "$FL_BASE/storage/fifo"

lappend PACKAGES "$OFM_PATH/comp/mi_tools/pkg/mi32_pkg.vhd"

lappend MOD "$ENTITY_BASE/fl_rxbuffer_ent.vhd"
lappend MOD "$ENTITY_BASE/fl_rxbuffer.vhd"

# Full FrameLink RX Buffer
if { $ARCHGRP == "FULL" } {
    lappend MOD "$ENTITY_BASE/fl_rxbuffer.vhd"

    set COMPONENTS [list \
        [ list "PKG_MATH"    $OFM_PATH/comp/base/pkg       "MATH"] \
        [ list "FL_FIFO"     $FIFO_BASE                    "FULL"] \
        [ list "GEN_MUX"     $OFM_PATH/comp/base/logic/mux "FULL"] \
    ]
}
