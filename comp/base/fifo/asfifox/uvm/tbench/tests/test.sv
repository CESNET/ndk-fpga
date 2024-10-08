//-- test.sv: Verification test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    bit timeout;
    uvm_asfifox::env #(ITEM_WIDTH)                 m_env;
    uvm_logic_vector::sequence_simple#(ITEM_WIDTH) h_seq_rx;
    uvm_mvb::sequence_simple_tx #(1, ITEM_WIDTH)   h_seq_tx;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_asfifox::env #(ITEM_WIDTH)::type_id::create("m_env", this);
    endfunction

    task test_wait_timeout(int unsigned time_length);
        #(time_length*1us);
    endtask

    task test_wait_result();
        do begin
            #(600ns);
        end while (m_env.m_scoreboard.used() != 0);
        timeout = 0;
    endtask

    task run_reset(uvm_phase phase, uvm_reset::agent m_agent);
            uvm_reset::sequence_start m_seq;

            m_seq = uvm_reset::sequence_start::type_id::create("m_seq", m_agent.m_sequencer);
            m_seq.randomize();
            m_seq.start(m_agent.m_sequencer);
    endtask

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    task run_seq_rx(uvm_phase phase);
        phase.raise_objection(this, "Start of rx sequence");
        for(int i = 0; i < 100; i++) begin
            h_seq_rx.randomize();
            h_seq_rx.start(m_env.rx_env.m_logic_vector_agent.m_sequencer);
        end

        timeout = 1;
        fork
            test_wait_timeout(20);
            test_wait_result();
        join_any;

        phase.drop_objection(this, "End of rx sequence");
    endtask


    task run_seq_tx(uvm_phase phase);
        forever begin
            h_seq_tx.randomize();
            h_seq_tx.start(m_env.tx_env.m_mvb_agent.m_sequencer);
        end
    endtask

    virtual task run_phase(uvm_phase phase);

        h_seq_rx = uvm_logic_vector::sequence_simple#(ITEM_WIDTH)::type_id::create("h_seq_rx");

        h_seq_tx = uvm_mvb::sequence_simple_tx #(1, ITEM_WIDTH)::type_id::create("h_seq_tx");

        fork
            run_reset(phase, m_env.rx_reset);
            run_reset(phase, m_env.tx_reset);
        join_none

        fork
            run_seq_tx(phase);
            run_seq_rx(phase);
        join
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        if (timeout) begin
            `uvm_error(this.get_full_name(), "\n\t===================================================\n\tTIMEOUT SOME PACKET STUCK IN DESIGN\n\t===================================================\n\n");
        end
    endfunction
endclass
