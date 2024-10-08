# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Ivan Bryndza <xbrynd00@stud.feec.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set FLU_BASE            "$ENTITY_BASE/../.."

# Base directories
set PKG_BASE    "$OFM_PATH/comp/base/pkg"
set MOD "$MOD $ENTITY_BASE/flu_bfm_rdy_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/flu_bfm_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/flu_bfm.vhd"
set MOD "$MOD $ENTITY_BASE/flu_monitor.vhd"


# components
set COMPONENTS [list \
  [ list "PKG_MATH"        $PKG_BASE         "MATH"] \
]

#set COMPONENTS [list \
#  [ list "PKG_MATH"        $PKG_BASE         "MATH"] \
#]
