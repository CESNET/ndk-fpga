// virtual_sequencer.sv: Virtual sequencer
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequencer #(
    int unsigned MFB_ITEM_WIDTH,
    int unsigned RX_MVB_ITEM_WIDTH
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mfb_frame_extender::virtual_sequencer #(MFB_ITEM_WIDTH, RX_MVB_ITEM_WIDTH))

    uvm_reset::sequencer                                                                                        m_reset;
    // verilog_lint: waive line-length
    sequencer_length_extractor  #(MFB_ITEM_WIDTH)                                                               m_rx_mfb;
    // verilog_lint: waive line-length
    uvm_logic_vector::sequencer #(RX_MVB_ITEM_WIDTH)                                                            m_rx_mvb;

    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
