// virtual_sequencer.sv: Virtual sequencer
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequencer #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned PKT_MTU) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mfb_frame_trimmer::virtual_sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU))

    uvm_reset::sequencer                                                                    m_reset;
    sequencer_length_extractor  #(ITEM_WIDTH)                                               m_rx_mfb_data;
    uvm_logic_vector::sequencer #(META_WIDTH+1+$clog2(PKT_MTU+1))                           m_rx_mfb_meta;
    uvm_mfb::sequencer          #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_tx_mfb;

    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
