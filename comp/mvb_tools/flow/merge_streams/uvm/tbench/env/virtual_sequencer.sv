// virtual_sequencer.sv: Virtual sequencer
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequencer #(int unsigned MVB_ITEMS, int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mvb_merge_streams::virtual_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    uvm_reset::sequencer                                     m_reset;
    uvm_logic_vector::sequencer #(MVB_ITEM_WIDTH)            m_rx_mvb[RX_STREAMS];
    uvm_mvb::sequencer          #(MVB_ITEMS, MVB_ITEM_WIDTH) m_tx_mvb;

    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
