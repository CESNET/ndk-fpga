# Modules.tcl: Component include tcl script.
# Copyright (C) 2018 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set FIFOX_PATH      "$OFM_PATH/comp/base/fifo/fifox"
set MUX_PATH        "$OFM_PATH/comp/base/logic/mux"
set FLU_FIFO_PATH   "$OFM_PATH/comp/flu_tools/storage/fifox"

set COMPONENTS [ list \
                 [ list "FIFOX"     $FIFOX_PATH      "FULL"] \
                 [ list "GEN_MUX"   $MUX_PATH        "FULL"] \
                 [ list "FLU_FIFOX" $FLU_FIFO_PATH   "FULL"] \
               ]

set MOD "$MOD $ENTITY_BASE/ent.vhd"
set MOD "$MOD $ENTITY_BASE/arch.vhd"
