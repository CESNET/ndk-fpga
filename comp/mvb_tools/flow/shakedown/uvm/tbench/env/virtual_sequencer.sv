// virtual_sequencer.sv: Virtual sequencer
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequencer #(int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mvb_shakedown::virtual_sequencer #(TX_ITEMS, ITEM_WIDTH))

    uvm_reset::sequencer                         m_reset;
    uvm_logic_vector::sequencer #(ITEM_WIDTH)    m_rx_mvb;
    uvm_mvb::sequencer          #(1, ITEM_WIDTH) m_tx_mvb[TX_ITEMS];

    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
