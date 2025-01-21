// test.sv: Verification test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);


    // declare the Environment reference variable
    uvm_framepacker::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX, RX_CHANNELS, USR_RX_PKT_SIZE_MAX, HDR_META_WIDTH) m_env;

    // ------------------------------------------------------------------------
    // Functions
    // Constrctor of the test object
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Build phase function, e.g. the creation of test's internal objects
    function void build_phase(uvm_phase phase);
        m_env = uvm_framepacker::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, SPACE_SIZE_MIN_RX, SPACE_SIZE_MAX_RX, SPACE_SIZE_MIN_TX, SPACE_SIZE_MAX_TX, RX_CHANNELS, USR_RX_PKT_SIZE_MAX, HDR_META_WIDTH)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    task run_seq(uvm_phase phase);
        time timeout;
        virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, USR_RX_PKT_SIZE_MAX) m_vseq;
        m_vseq = virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_CHANNELS, USR_RX_PKT_SIZE_MAX)::type_id::create("m_vseq");

        phase.raise_objection(this, "Start of rx sequence");
        m_vseq.init(FRAME_SIZE_MIN, FRAME_SIZE_MAX);

         //RUN MFB RX SEQUENCE
        m_vseq.randomize();
        m_vseq.start(m_env.vscr);

        timeout =  $time();
        while ((timeout + 0.5ms) > $time() && m_env.m_scoreboard.used() != 0) begin
            #(600ns);
        end

        phase.drop_objection(this, "End of rx sequence");
    endtask

    virtual task run_phase(uvm_phase phase);
        run_seq(phase);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        if (m_env.m_scoreboard.used()) begin
            `uvm_error(this.get_full_name(), "\n\t===================================================\n\tTIMEOUT SOME PACKET STUCK IN DESIGN\n\t===================================================\n\n");
        end
    endfunction

endclass
