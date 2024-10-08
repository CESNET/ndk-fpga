// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W) extends uvm_sequencer;

    `uvm_component_param_utils(uvm_pcie_adapter::virt_sequencer#(CQ_MFB_REGIONS, CC_MFB_REGIONS, RQ_MFB_REGIONS, RC_MFB_REGIONS, CQ_MFB_REGION_SIZE, CC_MFB_REGION_SIZE, RQ_MFB_REGION_SIZE, RC_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CC_MFB_BLOCK_SIZE, RQ_MFB_BLOCK_SIZE, RC_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CC_MFB_ITEM_WIDTH, RQ_MFB_ITEM_WIDTH, RC_MFB_ITEM_WIDTH, AVST_DOWN_META_W, AVST_UP_META_W, AXI_CQUSER_WIDTH, AXI_CCUSER_WIDTH, AXI_RCUSER_WIDTH, AXI_RQUSER_WIDTH, AXI_DATA_WIDTH, RQ_MFB_META_W, RC_MFB_META_W, CQ_MFB_META_W, CC_MFB_META_W))

    // AVALON Data Sequencers
    uvm_logic_vector_array::sequencer#(CQ_MFB_ITEM_WIDTH) m_avst_down_data_sqr;
    // AXI Data Sequencers
    uvm_logic_vector_array::sequencer#(CQ_MFB_ITEM_WIDTH) m_axi_cq_data_sqr;
    uvm_logic_vector_array::sequencer#(RC_MFB_ITEM_WIDTH) m_axi_rc_data_sqr;
    // MFB Data Sequencers
    uvm_logic_vector_array::sequencer#(RQ_MFB_ITEM_WIDTH) m_rq_mfb_data_sqr;
    uvm_logic_vector_array::sequencer#(CC_MFB_ITEM_WIDTH) m_cc_mfb_data_sqr;

    // AVALON Metadata Sequencers
    uvm_logic_vector::sequencer#(AVST_DOWN_META_W) m_avst_down_meta_sqr;
    // MFB Metadata Sequencers
    uvm_logic_vector::sequencer#(RQ_MFB_META_W)    m_rq_mfb_meta_sqr;
    uvm_logic_vector::sequencer#(CC_MFB_META_W)    m_cc_mfb_meta_sqr;

    // AVALON Ready Sequencer
    uvm_avst::sequencer #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W)  m_avst_up_rdy_sqr;
    // Credit Control Sequencers
    uvm_crdt::sequencer m_crdt_up_sqr;
    uvm_crdt::sequencer m_crdt_down_sqr;
    // AXI Ready Sequencers
    uvm_axi::sequencer #(AXI_DATA_WIDTH, AXI_CCUSER_WIDTH, CC_MFB_REGIONS) m_axi_cc_rdy_sqr;
    uvm_axi::sequencer #(AXI_DATA_WIDTH, AXI_RQUSER_WIDTH, RQ_MFB_REGIONS) m_axi_rq_rdy_sqr;
    // MFB DST RDY Sequencers
    uvm_mfb::sequencer #(RC_MFB_REGIONS, RC_MFB_REGION_SIZE, RC_MFB_BLOCK_SIZE, RC_MFB_ITEM_WIDTH, RC_MFB_META_W)    m_mfb_rc_dst_rdy_sqr;
    uvm_mfb::sequencer #(CQ_MFB_REGIONS, CQ_MFB_REGION_SIZE, CQ_MFB_BLOCK_SIZE, CQ_MFB_ITEM_WIDTH, CQ_MFB_META_W)    m_mfb_cq_dst_rdy_sqr;
    // Reset sequencer
    uvm_reset::sequencer m_reset;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
