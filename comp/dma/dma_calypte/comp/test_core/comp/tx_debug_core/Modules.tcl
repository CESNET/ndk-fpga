# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

set MFB_FRAME_LNG_BASE  "$OFM_PATH/comp/mfb_tools/logic/frame_lng"
set MI_ASYNC_BASE       "$OFM_PATH/comp/mi_tools/async"
set NP_LUTRAM_BASE      "$OFM_PATH/comp/base/mem/np_lutram"
set MEMX_COUNTER_BASE   "$OFM_PATH/comp/base/logic/cnt_multi_memx"
set AUX_SIGNALS_BASE    "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"
set MFB_GENERATOR_BASE  "$OFM_PATH/comp/mfb_tools/debug/generator"

lappend COMPONENTS [ list "MFB_FRAME_LNG"         $MFB_FRAME_LNG_BASE   "FULL" ]
lappend COMPONENTS [ list "MI_ASYNC"              "$MI_ASYNC_BASE"      "FULL" ]
lappend COMPONENTS [ list "NP_LUTRAM"             "$NP_LUTRAM_BASE"     "FULL" ]
lappend COMPONENTS [ list "CNT_MULTI_MEMX"        "$MEMX_COUNTER_BASE"  "FULL" ]
lappend COMPONENTS [ list "MFB_AUXILIARY_SIGNALS" "$AUX_SIGNALS_BASE"   "FULL" ]
lappend COMPONENTS [ list "MFB_GENERATOR_MI32"    "$MFB_GENERATOR_BASE" "FULL" ]

lappend MOD "$ENTITY_BASE/debug_core.vhd"
