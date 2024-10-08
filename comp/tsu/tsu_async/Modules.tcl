# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2009 CESNET
# Author: Jan Stourac <xstour03 at stud.fit.vutbr.cz>
#         Jiri Matousek <matousek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#


# Auxiliary paths
set BASE_BASE              "$COMP_BASE/base"

# Component paths
set ASFIFO_BASE            "$OFM_PATH/comp/base/fifo/asfifo"

# Paths to subcomponents with scoped constraints
set ASYNC_OPEN_LOOP_SMD_BASE "$OFM_PATH/comp/base/async/open_loop_smd"

# Use source files of the module
if { $ARCHGRP == "SRC" } {
   # Components
   set COMPONENTS [list \
      [list "ASFIFO" $ASFIFO_BASE "FULL"] \
   ]

   # Modules
   set MOD "$MOD $ENTITY_BASE/tsu_async.vhd"
}

# Use .dcp file of the module
# (Add also all subcomponents with scoped constraints. This hack is necessary
#  for correct constraint's application in full design.)
if { $ARCHGRP == "DCP" } {
   # Components
   set COMPONENTS [ list \
      [list "ASYNC_OPEN_LOOP_SMD" $ASYNC_OPEN_LOOP_SMD_BASE "FULL"] \
      [list "ASFIFO"              $ASFIFO_BASE              "FULL"] \
   ]

   # Modules
   set MOD "$MOD $ENTITY_BASE/synth/tsu_async.dcp"

   # All device tree scripts used by module
   if { [file exists "$ENTITY_BASE/synth/DevTree_paths.txt"] } {
      set MOD "$MOD [read [open "$ENTITY_BASE/synth/DevTree_paths.txt" "r"]]"
   }
}

lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/tsu_async_ooc.xdc USED_IN {synthesis out_of_context}]
