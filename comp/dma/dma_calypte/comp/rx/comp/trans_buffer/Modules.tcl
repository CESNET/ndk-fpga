# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set REG_FIFO_BASE "$OFM_PATH/comp/base/fifo/reg_fifo"

lappend COMPONENTS [list "REG_FIFO" $REG_FIFO_BASE "FULL"]

lappend MOD "$ENTITY_BASE/rx_dma_calypte_trans_buffer.vhd"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
