// test.sv: Verification test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    uvm_mvb_merge_streams_ordered::env #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)             m_env;
    uvm_mvb                      ::sequence_lib_tx #(MVB_ITEMS*RX_STREAMS, MVB_ITEM_WIDTH)  tx_mvb_seq_lib;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_mvb_merge_streams_ordered::env #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_env", this);
    endfunction


    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    task run_seq_rx(uvm_phase phase);
        virt_sequence#(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) m_vseq;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence#(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_vseq");

        for (int unsigned it = 0; it < 1; it++) begin
            assert(m_vseq.randomize());
            m_vseq.start(m_env.m_virt_sqcr);
        end

        begin
            time time_start = $time();
            while((time_start + 100us) > $time() &&  m_env.m_scbrd.cmp.used() != 0) begin
                #(400ns);
            end
        end

        phase.drop_objection(this, "End of rx sequence");
    endtask

    task run_seq_port_tx(uvm_phase phase);
        forever begin
            tx_mvb_seq_lib.randomize();
            tx_mvb_seq_lib.start(m_env.m_tx_mvb_env.m_sequencer);
        end
    endtask

    task run_seq_tx(uvm_phase phase);
        fork
            run_seq_port_tx(phase);
        join_none;
    endtask

    virtual task run_phase(uvm_phase phase);

        tx_mvb_seq_lib = uvm_mvb::sequence_lib_tx #(MVB_ITEMS*RX_STREAMS, MVB_ITEM_WIDTH)::type_id::create("tx_mvb_seq_lib");
        tx_mvb_seq_lib.init_sequence();
        tx_mvb_seq_lib.cfg.probability_set(60, 100);
        tx_mvb_seq_lib.min_random_count = 200;
        tx_mvb_seq_lib.max_random_count = 500;

        run_seq_tx(phase);
        run_seq_rx(phase);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
