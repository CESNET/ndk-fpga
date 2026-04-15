//-- sequencer.sv: Virtual sequencer
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class sequencer #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_asfifox::sequencer #(ITEMS, ITEM_WIDTH, TUSER_WIDTH))

    // rx reset sequencer
    uvm_reset::sequencer m_reset_rx;
    // tx reset sequencer
    uvm_reset::sequencer m_reset_tx;
    // rx sequencer
    uvm_axi::sequencer #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) m_rx;
    // Tx sequencer
    uvm_axi::sequencer #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) m_tx;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
