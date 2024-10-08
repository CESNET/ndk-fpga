//-- test.sv: Verification test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   David Beneš <xbenes52@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    bit timeout;
    uvm_mfb_pipe::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)           m_env;

    uvm_sequence #(uvm_mfb::sequence_item#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)) h_seq_tx;

    //Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_mfb_pipe::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_env", this);
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

    // Create environment and Run sequences o their sequencers
    task run_seq_rx(uvm_phase phase);
        virt_sequence#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_vseq;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_vseq");
        assert(m_vseq.randomize());
        m_vseq.start(m_env.vscr);

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
            h_seq_tx.start(m_env.mfb_tx_env.m_mfb_agent.m_sequencer);
        end
    endtask

    virtual task run_phase(uvm_phase phase);
        if (USE_DST_RDY == 0) begin
            uvm_mfb::sequence_full_speed_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) h_seq_speed_tx;
            h_seq_speed_tx = uvm_mfb::sequence_full_speed_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("h_seq_speed_tx");
            h_seq_tx = h_seq_speed_tx;
        end else begin
            uvm_mfb::sequence_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) h_seq_lib_tx;
            h_seq_lib_tx = uvm_mfb::sequence_lib_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("h_seq_lib_tx");
            h_seq_lib_tx.init_sequence();
            h_seq_lib_tx.min_random_count = 200;
            h_seq_lib_tx.max_random_count = 500;
            h_seq_tx = h_seq_lib_tx;
        end

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
