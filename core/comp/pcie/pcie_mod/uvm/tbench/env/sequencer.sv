// sequencer.sv: Virtual sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class sequencer#(
    int unsigned RC_MFB_REGIONS,
    int unsigned RC_MFB_REGION_SIZE,
    int unsigned RC_MFB_BLOCK_SIZE,

    int unsigned CQ_MFB_REGIONS,
    int unsigned CQ_MFB_REGION_SIZE,
    int unsigned CQ_MFB_BLOCK_SIZE,

    int unsigned ITEM_WIDTH,

    int unsigned DMA_PORTS,
    int unsigned PCIE_ENDPOINTS
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_pcie_top::sequencer#(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE,
                                                        CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE,
                                                        ITEM_WIDTH, DMA_PORTS, PCIE_ENDPOINTS))

    // RQ DMA
    uvm_dma::sequencer  m_dma_rq[PCIE_ENDPOINTS][DMA_PORTS];
    // RC DMA

    //DMA CQ
    //uvm_mfb::sequencer #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, ITEM_WIDTH, CQ_MFB_META_W) m_dma_cq[PCIE_ENDPOINTS][DMA_PORTS];
    //DMA CC
    //its very simular to pcie but only support pcie response transactions.
    uvm_pcie::sequencer m_dma_cc[PCIE_ENDPOINTS][DMA_PORTS];

    //MI Interface (CQ+CC)
    uvm_mi::sequencer_master#(32, 32)                     m_mi_sqr[PCIE_ENDPOINTS];

    //PCIE sequencer
    uvm_pcie::sequencer m_pcie_rc[PCIE_ENDPOINTS];
    uvm_pcie::sequencer m_pcie_cq[PCIE_ENDPOINTS];

    // Reset sequencer
    uvm_reset::sequencer m_dma_reset;
    uvm_reset::sequencer m_mi_reset;
    uvm_reset::sequencer m_pcie_sysrst_n;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction
endclass


