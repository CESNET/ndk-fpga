// virtual_sequencer.sv: Virtual sequencer
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequencer #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned USERMETA_WIDTH, int unsigned RX_MVB_ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mfb_frame_extender::virtual_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH))

    uvm_reset::sequencer                                                                                        m_reset;
    sequencer_length_extractor  #(MFB_ITEM_WIDTH)                                                               m_rx_mfb;
    uvm_logic_vector::sequencer #(RX_MVB_ITEM_WIDTH)                                                            m_rx_mvb;
    uvm_mfb::sequencer          #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH) m_tx_mfb;
    uvm_mvb::sequencer          #(MFB_REGIONS, USERMETA_WIDTH)                                                  m_tx_mvb;

    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
