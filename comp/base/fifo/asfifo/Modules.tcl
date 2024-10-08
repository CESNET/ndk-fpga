# Modules.tcl: Local include tcl script
# Copyright (C) 2005 CESNET
# Author: Martin Mikusek <martin.mikusek@liberouter.org>
#         Jakub Cabal    <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# Base directories
set DISTMEM_BASE    "$OFM_PATH/comp/base/mem/gen_lutram/compatibility"
set OPEN_LOOP_BASE  "$OFM_PATH/comp/base/async/open_loop_smd"

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   set PACKAGES	"$OFM_PATH/comp/base/pkg/math_pack.vhd"

   # List of components
   set COMPONENTS [list \
                  [list "DISTMEM"       $DISTMEM_BASE "FULL"]  \
                  [list "ASYNC_OPEN_LOOP_SMD"  $OPEN_LOOP_BASE "FULL"]  \
                  ]

   set MOD "$MOD $ENTITY_BASE/asfifo.vhd"

    lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/asfifo.xdc SCOPED_TO_REF asfifo PROCESSING_ORDER LATE]
}

# Source file for empty component - empty architecture
if { $ARCHGRP == "EMPTY" } {
}

# debug component
if { $ARCHGRP == "DEBUG" } {
}
