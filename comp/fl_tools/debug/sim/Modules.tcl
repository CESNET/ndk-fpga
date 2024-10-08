# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#         Libor Polcak <xpolca03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set FL_BASE            "$ENTITY_BASE/../.."
set FIFO_BASE          "$FL_BASE/storage/fifo"
set TRANSFORMER_BASE   "$FL_BASE/flow/transformer"

# Base directories
set PKG_BASE    "$OFM_PATH/comp/base/pkg"
set MOD "$MOD $ENTITY_BASE/../../pkg/fl_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/fl_sim_oper.vhd"
set MOD "$MOD $ENTITY_BASE/fl_sim_logging.vhd"
set MOD "$MOD $ENTITY_BASE/fl_sim.vhd"
set MOD "$MOD $ENTITY_BASE/fl_bfm_rdy_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/fl_bfm_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/fl_bfm.vhd"
set MOD "$MOD $ENTITY_BASE/monitor.vhd"


# components
set COMPONENTS [list \
  [ list "PKG_MATH"        $PKG_BASE         "MATH"] \
  [ list "FL_TRANSFORMER"  $TRANSFORMER_BASE "FULL"] \
  [ list "FL_FIFO"         $FIFO_BASE        "FULL"] \
]

#set COMPONENTS [list \
#  [ list "PKG_MATH"        $PKG_BASE         "MATH"] \
#]
