# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2014 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#


# Paths
set MATH_PKG     "$OFM_PATH/comp/base/pkg"

set PACKAGES   "$PACKAGES  $MATH_PKG/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/qdr_bram_ent.vhd"


# Setup architecture
set MOD "$MOD $ENTITY_BASE/qdr_bram_arch.vhd"

# Components
set COMPONENTS [list \
      [list "GEN_OR" $OFM_PATH/comp/base/logic/or "FULL"] \
      [list "GEN_AND" $OFM_PATH/comp/base/logic/and "FULL"]
]
