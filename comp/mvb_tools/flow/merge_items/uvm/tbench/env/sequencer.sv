// sequencer.sv: Virtual sequencer
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequencer #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(merge_items::virt_sequencer #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH))

    uvm_reset::sequencer                                    m_reset;
    uvm_logic_vector::sequencer #(RX0_ITEM_WIDTH)           m_mvb_data0_sqr;
    uvm_logic_vector::sequencer #(RX1_ITEM_WIDTH)           m_mvb_data1_sqr;
    uvm_mvb::sequencer          #(RX0_ITEMS, TX_ITEM_WIDTH) m_mvb_rdy_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
