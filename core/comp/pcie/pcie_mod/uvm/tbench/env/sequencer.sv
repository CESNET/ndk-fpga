// sequencer.sv: Virtual sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequencer#(
    RC_MFB_REGIONS,
    RC_MFB_REGION_SIZE,
    RC_MFB_BLOCK_SIZE,
    RC_MFB_META_W,

    CQ_MFB_REGIONS,
    CQ_MFB_REGION_SIZE,
    CQ_MFB_BLOCK_SIZE,
    CQ_MFB_META_W,

    ITEM_WIDTH,

    RQ_MFB_META_W,
    CC_MFB_META_W,
    DMA_PORTS,
    PCIE_ENDPOINTS) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_META_W,
                                                        CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_META_W,
                                                        ITEM_WIDTH, RQ_MFB_META_W, CC_MFB_META_W, DMA_PORTS, PCIE_ENDPOINTS))

    // RQ DMA
    uvm_dma::sequencer  m_dma_rq[PCIE_ENDPOINTS][DMA_PORTS];

    // RC DMA
    uvm_mfb::sequencer #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, ITEM_WIDTH, RC_MFB_META_W) m_dma_rc_mfb[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_mvb::sequencer #(RC_MFB_REGIONS, sv_dma_bus_pack::DMA_DOWNHDR_WIDTH) m_dma_rc_mvb[PCIE_ENDPOINTS][DMA_PORTS];

    //DMA CQ
    uvm_mfb::sequencer #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W) m_dma_cq[PCIE_ENDPOINTS][DMA_PORTS];
    //DMA CC
    uvm_logic_vector::sequencer#(CC_MFB_META_W)           m_dma_cc_meta[PCIE_ENDPOINTS][DMA_PORTS];
    uvm_logic_vector_array::sequencer#(ITEM_WIDTH) m_dma_cc_data[PCIE_ENDPOINTS][DMA_PORTS];
    //MI Interface (CQ+CC)
    uvm_mi::sequencer_master#(32, 32)                     m_mi_sqr[PCIE_ENDPOINTS];

    //PCIE sequencer
    uvm_pcie::sequencer                                   m_pcie[PCIE_ENDPOINTS];

    // Reset sequencer
    uvm_reset::sequencer m_dma_reset;
    uvm_reset::sequencer m_mi_reset;
    uvm_reset::sequencer m_pcie_sysrst_n;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass


