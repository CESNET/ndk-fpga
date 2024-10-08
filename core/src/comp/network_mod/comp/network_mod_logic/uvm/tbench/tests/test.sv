// test.sv: Verification test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause 


class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    net_mod_logic_env::env_base #(USER_REGIONS, USER_REGION_SIZE, CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, USER_MVB_WIDTH, ETH_CHANNELS, RX_MAC_LITE_REGIONS) m_env;
    int unsigned timeout;
    logic [ETH_CHANNELS-1:0] core_rx_wait;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = net_mod_logic_env::env_base #(USER_REGIONS, USER_REGION_SIZE, CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, USER_MVB_WIDTH, ETH_CHANNELS, RX_MAC_LITE_REGIONS)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Sequences

    virtual task core_tx_seq(uvm_phase phase, int unsigned index);
        uvm_mfb::sequence_lib_tx#(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) mfb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx#(CORE_REGIONS, CORE_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("core_tx_seq", this);
        mfb_seq.init_sequence();
        mfb_seq.min_random_count = 150;
        mfb_seq.max_random_count = 250;

        //RUN
        forever begin
            void'(mfb_seq.randomize());
            mfb_seq.start(m_env.m_core_tx_mfb_env[index].m_sequencer);
        end
    endtask

    virtual task core_rx_seq(uvm_phase phase, int unsigned index);
        uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH) m_byte_array_seq;

        m_byte_array_seq = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("core_rx_seq");
        m_byte_array_seq.init_sequence();
        m_byte_array_seq.min_random_count = 5*4;
        m_byte_array_seq.max_random_count = 10*4;

        //RUN
        for (int unsigned it = 0; it < 5; it++) begin
            void'(m_byte_array_seq.randomize());
            m_byte_array_seq.start(m_env.m_core_rx_mfb_env[index].m_sequencer.m_data);
        end
        core_rx_wait[index] = 1;
    endtask

    virtual task user_tx_seq(uvm_phase phase);
        uvm_mfb::sequence_lib_tx#(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) mfb_seq;
        uvm_mvb::sequence_lib_tx#(USER_REGIONS, USER_MVB_WIDTH                             ) mvb_seq;

        mfb_seq = uvm_mfb::sequence_lib_tx#(USER_REGIONS, USER_REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0)::type_id::create("mfb_user_tx_seq", this);
        mfb_seq.min_random_count = 70;
        mfb_seq.max_random_count = 150;
        mfb_seq.init_sequence();

        mvb_seq = uvm_mvb::sequence_lib_tx#(USER_REGIONS, USER_MVB_WIDTH)::type_id::create("mvb_user_tx_seq", this);
        mvb_seq.min_random_count = 70;
        mvb_seq.max_random_count = 150;
        mvb_seq.init_sequence();

        //RUN
        fork
            forever begin
                //mfb_seq.set_starting_phase(phase);
                void'(mfb_seq.randomize());
                mfb_seq.start(m_env.m_user_tx_mfb_env.m_sequencer);
            end
            forever begin
                //mvb_seq.set_starting_phase(phase);
                void'(mvb_seq.randomize());
                mvb_seq.start(m_env.m_user_tx_mvb_env.m_sequencer);
            end
        join_none;
    endtask

    // ------------------------------------------------------------------------
    // Create environment and Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        virt_seq #(ITEM_WIDTH, META_WIDTH, ETH_CHANNELS) m_vseq;
        net_mod_logic_env::sequence_simple#(ETH_CHANNELS) seq_mi;

        seq_mi = net_mod_logic_env::sequence_simple#(ETH_CHANNELS)::type_id::create("seq", this);
        seq_mi.regmodel = m_env.m_regmodel.m_regmodel;

        phase.raise_objection(this);

        #(2*RESET_CLKS*CLK_PERIOD_USER);
        seq_mi.start(null);
        #(1000*CLK_PERIOD_USER);

        //Run MFB TX (CORE) sequence
        for (int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            fork
                automatic int unsigned index = it;
                core_tx_seq(phase, index);
            join_none
        end

        //Run MFB RX (CORE) sequence
        core_rx_wait = '0;
        for (int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            fork
                automatic int unsigned index = it;
                core_rx_seq(phase, index);
            join_none
        end

        //Run MFB and MVB TX (USER) sequence
        user_tx_seq(phase);

        //Run MFB RX (USER) sequence
        m_vseq = virt_seq #(ITEM_WIDTH, META_WIDTH, ETH_CHANNELS)::type_id::create("m_vseq"); 
        m_vseq.randomize();
        m_vseq.start(m_env.m_user_rx_mfb_env.m_sequencer);

        for (int unsigned it = 0; it < ETH_CHANNELS; it++) begin
            wait(core_rx_wait[it] == 1);
        end

        // --------------------------------------------------------------------
        timeout = 1;
        fork
            test_wait_timeout(100);
            test_wait_result();
        join_any;

        phase.drop_objection(this);

    endtask

    task test_wait_timeout(int unsigned time_length);
        #(time_length*1us);
    endtask

    task test_wait_result();
        do begin
            #(600ns);
        end while (m_env.sc.used() != 0);
        timeout = 0;
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        if (timeout) begin
            `uvm_error(this.get_full_name(), "\n\t===================================================\n\tTIMEOUT SOME PACKET STUCK IN DESIGN\n\t===================================================\n\n");
        end
    endfunction

endclass
