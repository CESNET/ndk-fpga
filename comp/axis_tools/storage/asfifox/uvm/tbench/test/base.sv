//-- base.sv: Base test class
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class base #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_test;
    uvm_component_registry #(test::base#(ITEMS, ITEM_WIDTH, TUSER_WIDTH), "test::base") type_id;

    `m_uvm_get_type_name_func(test::base)

    // Test have to create top level environment
    uvm_asfifox::env #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) m_env;

    // Constructor
    function new(string name = "base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Create environment
    function void build_phase(uvm_phase phase);
        m_env = uvm_asfifox::env #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_end;

        phase.raise_objection(this);

        fork

            // Start Reset sequence / Reset DUT RX
            begin
                uvm_reset::sequence_start seq_rst_rx;

                seq_rst_rx = uvm_reset::sequence_start::type_id::create("seq_rst_rx", this);
                assert(seq_rst_rx.randomize()) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize reset sequence");
                end
                seq_rst_rx.start(m_env.m_sequencer.m_reset_rx);
            end

            // Start TX Reset sequence / Reset DUT TX
            begin
                uvm_reset::sequence_start seq_rst_tx;

                seq_rst_tx = uvm_reset::sequence_start::type_id::create("seq_rst_tx", this);
                assert(seq_rst_tx.randomize()) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize reset sequence");
                end
                seq_rst_tx.start(m_env.m_sequencer.m_reset_tx);
            end

        join_none

        fork
            // Start RX sequence. Generating input
            // Join when input stop
            begin
                uvm_asfifox::sequence_rx_base #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) seq;
                time seq_time_end;


                seq = uvm_asfifox::sequence_rx_base #(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("seq", this);

                seq.cfg = new();
                seq.cfg.frame_size_min = 1;
                seq.cfg.frame_size_max = 2048;

                for (int i=0; i<20; ++i) begin
                    assert(seq.randomize()) else begin
                        `uvm_fatal(this.get_full_name(), "\n\tCannot randomize RX sequence");
                    end
                    seq.start(m_env.m_sequencer.m_rx);
                end
            end

            // Start TX sequence. Low level agent need received RDY signal
            begin
                uvm_axi::sequence_lib_tx#(ITEMS, ITEM_WIDTH, TUSER_WIDTH) seq;

                seq = uvm_axi::sequence_lib_tx#(ITEMS, ITEM_WIDTH, TUSER_WIDTH)::type_id::create("seq", this);
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
