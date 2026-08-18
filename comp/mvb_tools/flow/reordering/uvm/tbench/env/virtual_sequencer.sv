// virtual_sequencer.sv: Virtual sequencer
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequencer #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_mvb_reordering::virtual_sequencer #(ITEMS, ITEM_WIDTH))

    uvm_reset::sequencer                          m_reset;
    uvm_mvb::sequencer #(ITEMS, ITEM_WIDTH  + $clog2(ITEMS))     m_rx_mvb;
    uvm_mvb::sequencer #(ITEMS, ITEM_WIDTH)     m_tx_mvb;

    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
