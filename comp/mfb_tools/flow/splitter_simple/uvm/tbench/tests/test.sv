//-- test.sv: Verification test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    uvm_splitter_simple::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, SPLITTER_OUTPUTS, META_BEHAV) m_env;
    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_splitter_simple::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, SPLITTER_OUTPUTS, META_BEHAV)::type_id::create("m_env", this);
    endfunction

    virtual task run_reset(uvm_phase phase);
        uvm_reset::sequence_reset reset;
        uvm_reset::sequence_run   run;

        reset = uvm_reset::sequence_reset::type_id::create("reset_reset");
        run   = uvm_reset::sequence_run::type_id::create("reset_run");
        run.length_min = 1000;
        run.length_max = 2000;

        //
        forever begin
            //reset.set_starting_phase(phase);
            void'(reset.randomize());
            reset.start(m_env.m_reset.m_sequencer);
            forever begin
                //run.set_starting_phase(phase);
                void'(run.randomize());
                run.start(m_env.m_reset.m_sequencer);
            end
        end
    endtask

    virtual task tx_seq(uvm_phase phase, int unsigned index);
        uvm_mfb::sequence_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) mfb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx#(REGIONS, REGION_SIZE, BLOCK_SIZE,  ITEM_WIDTH, META_WIDTH)::type_id::create("mfb_eth_tx_seq", this);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 100;
        mfb_seq.max_random_count = 200;

        //RUN ETH
        forever begin
            mfb_seq.randomize();
            mfb_seq.start(m_env.m_env_tx[index].m_sequencer);
        end
    endtask

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_start;
        virt_seq #(ITEM_WIDTH, META_WIDTH, SPLITTER_OUTPUTS) m_vseq;

        phase.raise_objection(this);

        fork
            run_reset(phase);
        join_none;


        //RUN MFB TX SEQUENCE
        for (int unsigned it = 0; it < SPLITTER_OUTPUTS; it++) begin
            fork
                automatic int unsigned index = it;
                tx_seq(phase, index);
            join_none
        end

        //RUN MFB RX SEQUENCE
        m_vseq = virt_seq #(ITEM_WIDTH, META_WIDTH, SPLITTER_OUTPUTS)::type_id::create("m_vseq");
        m_vseq.randomize();
        m_vseq.start(m_env.m_env_rx.m_sequencer);


        time_start = $time();
        while ((time_start + 10us) > $time() && m_env.sc.used() != 0) begin
            #(600ns);
        end

        phase.drop_objection(this);

    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
