# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MUX        "$OFM_PATH/comp/base/logic/mux"
set PAC_STATS  "$ENTITY_BASE/.."

set COMPONENTS [ list \
                  [ list "MUX_GEN"           $MUX          "FULL" ] \
                  [ list "PAC_STATS"         $PAC_STATS    "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/comp/cnt_trans.vhd"
set MOD "$MOD $ENTITY_BASE/comp/init_stats.vhd"
set MOD "$MOD $ENTITY_BASE/comp/cnt_wait.vhd"
set MOD "$MOD $ENTITY_BASE/comp/tr_wait.vhd"
set MOD "$MOD $ENTITY_BASE/comp/filter_trans.vhd"
set MOD "$MOD $ENTITY_BASE/comp/mi32_control.vhd"
set MOD "$MOD $ENTITY_BASE/comp/mux_tr.vhd"
set MOD "$MOD $ENTITY_BASE/control_stats_top_ent.vhd"
set MOD "$MOD $ENTITY_BASE/control_stats_top_arch.vhd"
