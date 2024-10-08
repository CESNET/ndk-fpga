# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/dma/dma_calypte/comp/rx/comp/hdr_manager/pkg/dma_hdr_pkg.vhd"

set MFB_DROPPER_BASE    "$OFM_PATH/comp/mfb_tools/flow/dropper"
set FIFOX_MULTI_BASE    "$OFM_PATH/comp/base/fifo/fifox_multi"

lappend COMPONENTS [ list "MFB_DROPPER"     $MFB_DROPPER_BASE   "FULL"]
lappend COMPONENTS [ list "FIFOX_MULTI"     $FIFOX_MULTI_BASE   "FULL"]

lappend MOD "$ENTITY_BASE/tx_dma_chan_start_stop_ctrl.vhd"
