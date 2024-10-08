// test.sv: Verification test
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//         Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test)

    uvm_mvb_demux::env #(ITEMS, ITEM_WIDTH, TX_PORTS) m_env;
    uvm_mvb::sequence_lib_tx#(ITEMS, ITEM_WIDTH)      m_tx_mvb_seq_lib [TX_PORTS -1 : 0];

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_mvb_demux::env #(ITEMS, ITEM_WIDTH, TX_PORTS)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    task run_seq_rx(uvm_phase phase);
        virt_sequence#(ITEM_WIDTH, TX_PORTS) m_vseq;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence#(ITEM_WIDTH, TX_PORTS)::type_id::create("m_vseq");

        assert(m_vseq.randomize());
        m_vseq.start(m_env.m_virt_sqcr);

        begin
            time time_start = $time();
            while((time_start + 100us) > $time() &&  m_env.m_scoreboard.used() != 0) begin
                #(400ns);
            end
        end

        phase.drop_objection(this, "End of rx sequence");
    endtask

    task run_seq_port_tx(uvm_phase phase, int port);
        forever begin
            m_tx_mvb_seq_lib[port].randomize();
            m_tx_mvb_seq_lib[port].start(m_env.m_tx_mvb_env[port].m_mvb_agent.m_sequencer);
        end
    endtask

    task run_seq_tx(uvm_phase phase);
        for (int port = 0; port < TX_PORTS; port++) begin
            fork
                automatic int port_idx = port;
                run_seq_port_tx(phase, port_idx);
            join_none;
        end
    endtask

    virtual task run_phase(uvm_phase phase);

        for (int it = 0; it < TX_PORTS; it++) begin
            m_tx_mvb_seq_lib[it] = uvm_mvb::sequence_lib_tx #(ITEMS, ITEM_WIDTH)::type_id::create($sformatf("m_tx_mvb_seq_lib_%0d", it));
            m_tx_mvb_seq_lib[it].init_sequence();
            m_tx_mvb_seq_lib[it].cfg.probability_set(60, 100);
            m_tx_mvb_seq_lib[it].min_random_count = 200;
            m_tx_mvb_seq_lib[it].max_random_count = 500;
        end

        run_seq_tx(phase);
        run_seq_rx(phase);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
