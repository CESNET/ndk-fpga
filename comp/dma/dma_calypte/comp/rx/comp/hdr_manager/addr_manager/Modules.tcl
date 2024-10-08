# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set GEN_LUTRAM_BASE "$OFM_PATH/comp/base/mem/gen_lutram"

lappend COMPONENTS [list "GEN_LUTRAM" $GEN_LUTRAM_BASE "FULL"]

lappend MOD "$ENTITY_BASE/rx_dma_calypte_addr_manager.vhd"
