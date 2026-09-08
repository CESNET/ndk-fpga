// virtual_sequence_base.sv: Virtual base sequence
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_base #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_sequence;
    `uvm_object_param_utils(test::virtual_sequence_base #(ITEMS, ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_mvb_reordering::virtual_sequencer #(ITEMS, ITEM_WIDTH))

    // verilog_lint: waive line-length
    uvm_reset::sequence_start  m_reset;
    // verilog_lint: waive line-length

    sequence_mvb#(ITEMS, ITEM_WIDTH)                m_rx_mvb;

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
        m_rx_mvb = sequence_mvb#(ITEMS, ITEM_WIDTH)::type_id::create("m_rx_mvb");

        // Configure the RX MVB sequence
        m_rx_mvb.transaction_count_min = ITEMS*300;
        m_rx_mvb.transaction_count_max = ITEMS*500;
    endfunction

    task body();
        init();

        // Run the reset sequence
        fork
            begin
                assert(m_reset.randomize());
                m_reset.start(p_sequencer.m_reset);
            end
            begin
                uvm_mvb::sequence_lib_tx #(ITEMS, ITEM_WIDTH) mvb_seq;

                mvb_seq = uvm_mvb::sequence_lib_tx #(ITEMS, ITEM_WIDTH)::type_id::create("mvb_seq");
                mvb_seq.init_sequence();
                mvb_seq.min_random_count =  100;
                mvb_seq.max_random_count = 2000;

                forever begin
                    assert(mvb_seq.randomize()) else begin
                        `uvm_fatal(this.get_full_name(), "\n\tCannot randomize TX sequence\n");
                    end
                    mvb_seq.start(p_sequencer.m_tx_mvb);
                end
            end
        join_none

        #(400ns);

        // Run the RX MVB sequence
        for(int unsigned it = 0; it < 100; it++) begin
            assert(m_rx_mvb.randomize());
            m_rx_mvb.start(p_sequencer.m_rx_mvb);
        end
    endtask

endclass
