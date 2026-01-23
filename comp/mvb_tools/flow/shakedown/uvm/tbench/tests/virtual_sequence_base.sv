// virtual_sequence_base.sv: Virtual base sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_base #(int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virtual_sequence_base #(TX_ITEMS, ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_mvb_shakedown::virtual_sequencer #(TX_ITEMS, ITEM_WIDTH))

    uvm_reset::sequence_start                          m_reset;
    uvm_logic_vector::sequence_simple #(ITEM_WIDTH)    m_rx_mvb;

    function new(string name = "virtual_sequence_base");
        super.new(name);
    endfunction

    virtual function void init();
        // Create the reset sequence
        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        // --------------- //
        // RX MVB sequence //
        // --------------- //

        // Create the RX MVB sequence
        m_rx_mvb = uvm_logic_vector::sequence_simple #(ITEM_WIDTH)::type_id::create("m_rx_mvb");
        // Configure the RX MVB sequence
        m_rx_mvb.transaction_count_min = TX_ITEMS*300;
        m_rx_mvb.transaction_count_max = TX_ITEMS*500;
    endfunction

    task body();
        // Run the reset sequence
        fork
            begin
                assert(m_reset.randomize());
                m_reset.start(p_sequencer.m_reset);
            end
        join_none

        #(100ns);

        // Run the RX MVB sequence
        begin
            assert(m_rx_mvb.randomize());
            m_rx_mvb.start(p_sequencer.m_rx_mvb);
        end
    endtask

endclass
