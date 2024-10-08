# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

set QDR_BASE  "$COMP_BASE/proc/sdm/qdr"

# Paths
set MATH_PKG     "$OFM_PATH/comp/base/pkg"
set ASFIFO_BASE   "$OFM_PATH/comp/base/fifo/asfifo_bram_xilinx"

set PACKAGES   "$PACKAGES  $MATH_PKG/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/qdr_ent.vhd"


# Setup architecture
set MOD "$MOD $ENTITY_BASE/qdr_arch.vhd"

# Components
set COMPONENTS [list \
      [list "ASFIFO_BRAM"     $ASFIFO_BASE   ] \
      [list "GEN_OR" $OFM_PATH/comp/base/logic/or "FULL"] \
      [list "GEN_AND" $OFM_PATH/comp/base/logic/and "FULL"]

]
