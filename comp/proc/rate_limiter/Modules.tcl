# Modules.tcl: Component include tcl script.
# Copyright (C) 2015 CESNET
# Author: Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MEM                       "$OFM_PATH/comp/base/mem/dp_bmem_V7"
set CORE                      "$COMP_BASE/proc/rate_limiter/rate_limiter_core"

set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
set COMPONENTS [ list \
                  [ list "DP_BRAM_V7"     $MEM    "STRUCTUAL" ] \
                  [ list "RATE_LIM_MEM"   $CORE   "STRUCTUAL" ] \
               ]

set MOD "$MOD $ENTITY_BASE/rate_limiter_mi32_ent.vhd"
set MOD "$MOD $ENTITY_BASE/rate_limiter_mi32_arch.vhd"
set MOD "$MOD $ENTITY_BASE/rate_limiter_top_ent.vhd"
set MOD "$MOD $ENTITY_BASE/rate_limiter_top_arch.vhd"
