# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Radek Iša <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "RX_DMA_CALYPTE_ADDR_MANAGER" "$ENTITY_BASE/addr_manager"          "FULL" ]
lappend COMPONENTS [ list "FIFOX"                       "$OFM_PATH/comp/base/fifo/fifox"     "FULL" ]
lappend COMPONENTS [ list "SH_FIFO"                     "$OFM_PATH/comp/base/fifo/sh_fifo"   "FULL" ]
lappend COMPONENTS [ list "PCIE_RQ_HDR_GEN"             "$OFM_PATH/comp/pcie/others/hdr_gen" "FULL" ]

lappend MOD "$ENTITY_BASE/rx_dma_calypte_hdr_manager.vhd"
