// sequencer.sv: Virtual sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mvb_merge_streams_ordered::virt_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    uvm_reset::sequencer                                        m_reset_sqcr;
    uvm_logic_vector::sequencer #(MVB_ITEM_WIDTH)               m_rx_mvb_sqcr [RX_STREAMS -1 : 0];
    uvm_logic_vector::sequencer #($clog2(RX_STREAMS))           m_rx_sel_mvb_sqcr;
    uvm_mvb::sequencer #(MVB_ITEMS*RX_STREAMS, MVB_ITEM_WIDTH)  m_tx_mvb_sqcr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
