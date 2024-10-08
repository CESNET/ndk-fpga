# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2016 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE     "$OFM_PATH/comp/base/pkg"
set FIFO_BASE    "$OFM_PATH/comp/base/fifo/fifo_bram"
set DEC_BASE     "$OFM_PATH/comp/base/logic/dec1fn"

# Entities
set MOD "$MOD $ENTITY_BASE/busreplay.vhd"

# components
set COMPONENTS [list \
  [list "PKG_MATH"        $PKG_BASE       "MATH"] \
  [list "FIFO"            $FIFO_BASE      "FULL"] \
  [list "DEC"             $DEC_BASE       "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
