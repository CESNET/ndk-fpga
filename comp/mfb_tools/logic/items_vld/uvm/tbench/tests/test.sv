// test.sv: Verification test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    typedef uvm_component_registry#(test::ex_test, "test::ex_test") type_id;

    // declare the Environment reference variable
    uvm_items_valid::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, MVB_ITEMS, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) m_env;
    uvm_reset::sequence_start                              m_reset;
    uvm_mvb::sequence_lib_tx#(MVB_ITEMS, MVB_DATA_WIDTH)   m_mvb_seq;

    // ------------------------------------------------------------------------
    // Functions
    // Constrctor of the test object
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction


    // Build phase function, e.g. the creation of test's internal objects
    function void build_phase(uvm_phase phase);
        // Initializing the reference to the environment
        m_env = uvm_items_valid::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, MVB_ITEMS, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("m_env", this);
    endfunction

    virtual task tx_mvb_seq();
        forever begin
            m_mvb_seq.randomize();
            m_mvb_seq.start(m_env.m_env_tx_mvb.m_sequencer);
        end
    endtask

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(m_env.m_reset.m_sequencer);
    endtask

    virtual function void init();

        m_reset   = uvm_reset::sequence_start::type_id::create("m_reset_seq");
        m_mvb_seq = uvm_mvb::sequence_lib_tx#(MVB_ITEMS, MVB_DATA_WIDTH)::type_id::create("m_mvb_seq");

        m_mvb_seq.init_sequence();
        m_mvb_seq.min_random_count = 100;
        m_mvb_seq.max_random_count = 200;

    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) m_vseq;
        time time_start;

        phase.raise_objection(this);

        //RUN MFB RX SEQUENCE
        m_vseq = virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("m_vseq");

        init();

        fork
            run_reset();
        join_none

        #(100ns);

        //RUN VSEQ and MVB TX SEQUENCE
        fork
            tx_mvb_seq();
        join_none

        m_vseq.randomize();
        m_vseq.start(m_env.vscr);

        time_start = $time();
        while((time_start + 1ms) > $time() && m_env.sc.used() != 0) begin
            #(300ns);
        end

        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
