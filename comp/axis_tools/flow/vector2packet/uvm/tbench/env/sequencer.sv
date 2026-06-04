// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

class sequencer #(
    int unsigned RX_ITEMS,
    int unsigned RX_ITEM_WIDTH,
    int unsigned TX_ITEMS,
    int unsigned TX_ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_vector2packet::sequencer #(
        RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH
    ))

    // reset sequencer
    uvm_reset::sequencer m_reset;
    // rx sequencer
    uvm_axi::sequencer #(RX_ITEMS, RX_ITEM_WIDTH, TUSER_WIDTH) m_rx;
    // tx sequencer
    uvm_axi::sequencer #(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) m_tx;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
