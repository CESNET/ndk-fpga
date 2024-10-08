//-- test.sv: Verification test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    bit timeout;
    uvm_pcie_cc_mfb2axi::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_TDATA_WIDTH, CC_TUSER_WIDTH, STRADDLING) m_env;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_pcie_cc_mfb2axi::env #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, CC_TDATA_WIDTH, CC_TUSER_WIDTH, STRADDLING)::type_id::create("m_env", this);
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

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    task run_seq_rx(uvm_phase phase);
        virt_sequence#(CC_TDATA_WIDTH, CC_TUSER_WIDTH, MFB_REGIONS, MFB_ITEM_WIDTH) m_vseq;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence#(CC_TDATA_WIDTH, CC_TUSER_WIDTH, MFB_REGIONS, MFB_ITEM_WIDTH)::type_id::create("m_vseq");
        assert(m_vseq.randomize());
        m_vseq.start(m_env.vscr);

        timeout = 1;
        fork
            test_wait_timeout(20);
            test_wait_result();
        join_any;

        phase.drop_objection(this, "End of rx sequence");
    endtask

    virtual task run_phase(uvm_phase phase);
        run_seq_rx(phase);
    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        if (timeout) begin
            `uvm_error(this.get_full_name(), "\n\t===================================================\n\tTIMEOUT SOME PACKET STUCK IN DESIGN\n\t===================================================\n\n");
        end
    endfunction
endclass
