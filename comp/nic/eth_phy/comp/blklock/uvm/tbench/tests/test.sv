/*
 * file       : test.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: Tests for Block Lock
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

class basic_test extends uvm_test;
    `uvm_component_utils(test::basic_test)

    uvm_blklock::env#(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME) m_env;

    test::simple_sequence simple_sequence;
    test::simple_invalid_sequence simple_inv_sequence;
    test::distributed_burst_sequence#(64, 8) burst_seq;
    test::distributed_sequence#(16, 64) burst_seq2;
    test::distributed_burst_sequence#(16, 64) burst_seq3;
    test::distributed_sequence#(64, 8) burst_seq4;
    test::distributed_burst_sequence#(16, 64) burst_seq5;

    uvm_reset::sequence_reset reset_sequence;
    uvm_reset::sequence_run run_sequence;

    int unsigned timeout;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_blklock::env#(SH_CNT_MAX, SH_INVALID_CNT_MAX, SLIP_WAIT_TIME)::type_id::create("m_env", this);

        reset_sequence = uvm_reset::sequence_reset::type_id::create("reset_sequence");
        reset_sequence.randomize();

        run_sequence = uvm_reset::sequence_run::type_id::create("run_sequence");
        run_sequence.length_max = 20000;
        run_sequence.length_min = 5000;
        run_sequence.randomize();

        simple_sequence = test::simple_sequence::type_id::create("simple_sequence");
        simple_sequence.max_trans = 3000;
        simple_sequence.randomize();

        simple_inv_sequence =  test::simple_invalid_sequence::type_id::create("simple_inv_sequence");
        simple_inv_sequence.max_trans = 3000;
        simple_inv_sequence.randomize();

        burst_seq2 = test::distributed_sequence#(16, 64)::type_id::create("burst_seq2");
        burst_seq2.max_trans = 3000;
        burst_seq2.randomize();

        burst_seq3 = test::distributed_burst_sequence#(16, 64)::type_id::create("burst_seq3");
        burst_seq3.max_trans = 3000;
        burst_seq3.randomize();

        burst_seq4 = test::distributed_sequence#(64, 8)::type_id::create("burst_seq4");
        burst_seq4.max_trans = 3000;
        burst_seq4.randomize();

        burst_seq5 = test::distributed_burst_sequence#(16, 64)::type_id::create("burst_seq5");
        burst_seq5.max_trans = 3000;
        burst_seq5.randomize();

        burst_seq = test::distributed_burst_sequence#(64, 8)::type_id::create("burst_seq");
        burst_seq.max_trans = 3000;
        burst_seq.randomize();
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        fork
            reset_sequence.start(m_env.reset_agent.m_sequencer);
        join;

        fork
            run_sequence.start(m_env.reset_agent.m_sequencer);
        join_none;


        simple_sequence.start(m_env.agent_rx.m_sequencer);

        simple_inv_sequence.start(m_env.agent_rx.m_sequencer);

        burst_seq2.start(m_env.agent_rx.m_sequencer);
        burst_seq3.start(m_env.agent_rx.m_sequencer);
        burst_seq4.start(m_env.agent_rx.m_sequencer);
        burst_seq5.start(m_env.agent_rx.m_sequencer);

        burst_seq.start(m_env.agent_rx.m_sequencer);

        simple_sequence.max_trans = 200;
        simple_sequence.min_trans = 100;
        simple_sequence.randomize();
        simple_sequence.start(m_env.agent_rx.m_sequencer);

        burst_seq.randomize();
        burst_seq.start(m_env.agent_rx.m_sequencer);

        #(1us)
        wait fork;

        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction

endclass
