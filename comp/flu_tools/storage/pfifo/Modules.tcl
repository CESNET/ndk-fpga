# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FLU_ASFIFO_BASE     "$OFM_PATH/comp/flu_tools/storage/asfifo"
set FLU_ASFIFO_X_BASE   "$OFM_PATH/comp/flu_tools/storage/asfifo_bram_xilinx"
set FLU_PIPE_BASE       "$OFM_PATH/comp/flu_tools/flow/pipe"
set FLU_FIFO_BASE       "$OFM_PATH/comp/flu_tools/storage/fifo"
set MATH_PKG_BASE       "$OFM_PATH/comp/base/pkg"

# Entities
set MOD "$MOD $ENTITY_BASE/pfifo_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo_core_arch.vhd"

set MOD "$MOD $ENTITY_BASE/pfifo_ent.vhd"
set MOD "$MOD $ENTITY_BASE/pfifo_arch.vhd"

# Subcomponents
set COMPONENTS [list [list "PKG"                $MATH_PKG_BASE       "MATH"] \
                     [list "FLU_ASFIFO"         $FLU_ASFIFO_BASE     "FULL"] \
                     [list "FLU_FIFO"           $FLU_FIFO_BASE       "FULL"] \
                     [list "FLU_ASFIFO_X"       $FLU_ASFIFO_X_BASE   "FULL"] \
                     [list "FLU_PIPE"           $FLU_PIPE_BASE       "FULL"]]
