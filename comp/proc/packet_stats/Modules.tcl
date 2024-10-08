# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set BRAM       "$OFM_PATH/comp/base/mem/dp_bmem_V7"

set COMPONENTS [ list \
                  [ list "DP_BRAM_V7"           $BRAM          "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/comp/alu_stats.vhd"
set MOD "$MOD $ENTITY_BASE/comp/cnt_stats.vhd"
set MOD "$MOD $ENTITY_BASE/comp/mem_stats.vhd"
set MOD "$MOD $ENTITY_BASE/comp/stats.vhd"
set MOD "$MOD $ENTITY_BASE/comp/trans.vhd"
set MOD "$MOD $ENTITY_BASE/pac_stats_top_ent.vhd"
set MOD "$MOD $ENTITY_BASE/pac_stats_top_arch.vhd"
