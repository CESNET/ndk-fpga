//-- base.sv: Base test class
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class base #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_test;
    uvm_component_registry #(test::base#(ITEMS, ITEM_WIDTH), "test::base") type_id;

    `m_uvm_get_type_name_func(test::base)

    // Test have to create top level environment
    uvm_asfifox::env #(ITEMS, ITEM_WIDTH) m_env;

    // Constructor
    function new(string name = "base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Create environment
    function void build_phase(uvm_phase phase);
        m_env = uvm_asfifox::env #(ITEMS, ITEM_WIDTH)::type_id::create("m_env", this);
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

        // Start RX sequence. Generating input
        begin
            uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH) seq_rx;
            uvm_logic_vector_array::config_sequence cfg;
            seq_rx = uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH)::type_id::create("seq_rx", this);

            // Instantiate and set up the configuration object BEFORE randomizing
            cfg = new();
            cfg.array_size_min = 1;
            cfg.array_size_max = 2048;

            seq_rx.min_random_count = 10;
            seq_rx.max_random_count = 20;

            seq_rx.init_sequence(cfg);

            // Run for ~5 minutes
            for (int i=0; i<20; ++i) begin
                assert(seq_rx.randomize()) else begin
                    `uvm_fatal(this.get_full_name(), "\n\tCannot randomize RX sequence");
                end
                seq_rx.start(m_env.m_sequencer.m_rx);
            end
        end

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
