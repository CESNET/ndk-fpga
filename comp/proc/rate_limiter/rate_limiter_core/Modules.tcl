# Modules.tcl: Component include tcl script.
# Copyright (C) 2015 CESNET
# Author: Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set ALU                       "$OFM_PATH/comp/base/logic/alu"
set CMP                       "$OFM_PATH/comp/base/logic/cmp"
set MUL48                     "$OFM_PATH/comp/base/logic/mul48"
set CNT                       "$OFM_PATH/comp/base/logic/cnt"
set MEM                       "$OFM_PATH/comp/base/mem/dp_bmem_V7"

set PACKAGES "$CNT/cnt_types.vhd"
set COMPONENTS [ list \
                  [ list "ALU_DSP"     $ALU    "STRUCTUAL" ] \
                  [ list "CMP_DSP"     $CMP    "STRUCTUAL" ] \
                  [ list "MUL48"       $MUL48  "STRUCTUAL" ] \
                  [ list "CNT"         $CNT    "FULL"      ] \
                  [ list "DP_BRAM_V7"  $MEM    "STRUCTUAL" ] \
               ]

set MOD "$MOD $ENTITY_BASE/rate_limiter_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/rate_limiter_core_arch.vhd"
set MOD "$MOD $ENTITY_BASE/rate_limiter_mem.vhd"
