// test.sv: Verification test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_test;
    typedef uvm_component_registry#(test::ex_test#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH), "test::ex_test") type_id;

    localparam string DUT_PATH = "testbench.DUT_U.VHDL_DUT_U";
    // declare the Environment reference variable
    uvm_rx_mac_lite_buffer::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, DUT_PATH) m_env;

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
        m_env = uvm_rx_mac_lite_buffer::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, DUT_PATH)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        time time_start;
        virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, test_param::FRAME_SIZE_MIN, test_param::FRAME_SIZE_MAX) m_vseq;
        m_vseq = virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, test_param::FRAME_SIZE_MIN, test_param::FRAME_SIZE_MAX)::type_id::create("m_vseq");

        phase.raise_objection(this);
        m_vseq.init(phase);

        //RUN MFB RX SEQUENCE
        m_vseq.randomize();
        m_vseq.start(m_env.vscr);

        time_start = $time();
        while ((time_start + 200us) > $time() && m_env.sc.used() != 0) begin
            #(300ns);
        end

        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction
endclass
