// sequencer.sv: Virtual sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Válek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer #(
    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,
    int unsigned CHANNELS,
    int unsigned HDR_META_WIDTH,
    int unsigned PKT_SIZE_MAX
) extends uvm_sequencer;

    `uvm_component_param_utils(uvm_tx_dma_calypte::sequencer #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, CHANNELS, HDR_META_WIDTH, PKT_SIZE_MAX))

    localparam USER_META_WIDTH = HDR_META_WIDTH + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);

    uvm_reset::sequencer                                                                                                m_reset_sqcr;
    uvm_tx_dma_calypte_cq::sequencer                                                                                    m_packet_sqcr [CHANNELS];
    uvm_mfb::sequencer #(USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, USER_META_WIDTH) m_usr_mfb_sqcr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
