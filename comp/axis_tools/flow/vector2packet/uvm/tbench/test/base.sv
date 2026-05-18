// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>
// SPDX-License-Identifier: BSD-3-Clause

class base#(
    int unsigned RX_ITEMS,
    int unsigned RX_ITEM_WIDTH,
    int unsigned TX_ITEMS,
    int unsigned TX_ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_test;
    uvm_component_registry #(test::base#(
        RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH
    ), "test::base") type_id;

    // test has to create top-level environment
    uvm_vector2packet::env #(RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) m_env;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_vector2packet::env #(
            RX_ITEMS, RX_ITEM_WIDTH, TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH
        )::type_id::create("m_env", this);
    endfunction

    //------------------------------------------------------------------------
    // run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_end;

        phase.raise_objection(this);

        fork
            // Reset DUT
            begin
            uvm_reset::sequence_start seq_rst;

            seq_rst = uvm_reset::sequence_start::type_id::create("seq_rst", this);
            assert(seq_rst.randomize()) else begin
                `uvm_fatal(this.get_full_name(), "\n\tCannot randomize reset sequence"); end
            seq_rst.start(m_env.m_sequencer.m_reset);
            end

        join_none

        #(100us);

        fork
            // Start RX sequence. Generating input
            // Join when input stop
            begin
                uvm_vector2packet::sequence_rx_base #(RX_ITEMS, RX_ITEM_WIDTH, TUSER_WIDTH) seq;
                time seq_time_end;

                seq = uvm_vector2packet::sequence_rx_base #(
                    RX_ITEMS, RX_ITEM_WIDTH, TUSER_WIDTH
                )::type_id::create("seq", this);

                seq.cfg = new();
                seq.cfg.frame_size_min = 1;
                seq.cfg.frame_size_max = 2048;

                assert(seq.randomize()) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize RX sequence");
                end
                seq.start(m_env.m_sequencer.m_rx);
            end

            // Start TX sequence. Low level agent need received RDY signal
            begin
                uvm_axi::sequence_lib_tx#(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH) seq;

                seq = uvm_axi::sequence_lib_tx#(TX_ITEMS, TX_ITEM_WIDTH, TUSER_WIDTH)::type_id::create("seq", this);
                seq.init_sequence();
                seq.min_random_count =  100;
                seq.max_random_count = 2000;

                forever begin
                    assert(seq.randomize()) else begin
                        `uvm_fatal(this.get_full_name(), "\n\tCannot randomize TX sequence\n");
                    end
                    seq.start(m_env.m_sequencer.m_tx);
                end
            end
        join_any

        #(100us);

        // Wait for all transactions to leave the DUT
        time_end = $time + 1000us;
        while ($time < time_end && m_env.used() == 1) begin
            #(500ns);
        end

        phase.drop_objection(this);

    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
