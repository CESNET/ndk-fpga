# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set BRAM   "$OFM_PATH/comp/base/mem/dp_bmem_V7"
set MUX    "$OFM_PATH/comp/base/logic/mux"
set DEMUX  "$OFM_PATH/comp/base/logic/demux"
set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set COMPONENTS [list \
    [list "DP_BRAM_V7"    $BRAM     "FULL"] \
    [list "GEN_MUX"       $MUX      "FULL"] \
    [list "GEN_DEMUX"     $DEMUX    "FULL"] \
]
set MOD "$MOD $ENTITY_BASE/rand_generator.vhd"
set MOD "$MOD $ENTITY_BASE/rw_registers.vhd"
set MOD "$MOD $ENTITY_BASE/cmp_wr_bram.vhd"
set MOD "$MOD $ENTITY_BASE/bram_generic.vhd"
set MOD "$MOD $ENTITY_BASE/generator.vhd"
set MOD "$MOD $ENTITY_BASE/streaming_generator.vhd"
