# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"

set MI_PIPE_BASE        "$OFM_PATH/comp/mi_tools/pipe"
set NP_LUTRAM_BASE      "$OFM_PATH/comp/base/mem/np_lutram"
set DSP_COMP_BASE       "$OFM_PATH/comp/base/dsp/dsp_comparator"
set MEMX_COUNTER_BASE   "$OFM_PATH/comp/base/logic/cnt_multi_memx"

lappend COMPONENTS \
    [ list "MI_PIPE"            "$MI_PIPE_BASE"                         "FULL" ] \
    [ list "NP_LUTRAM"          "$NP_LUTRAM_BASE"                       "FULL" ] \
    [ list "DSP_COMPARATOR"     "$DSP_COMP_BASE"                        "FULL" ] \
    [ list "CNT_MULTI_MEMX"     "$MEMX_COUNTER_BASE"                    "FULL" ] \

lappend MOD "$ENTITY_BASE/rx_dma_calypte_sw_manager.vhd"
