// test.sv: Verification test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    // declare the Environment reference variable
    uvm_ptc_mfb2pcie_axi::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, DATA_WIDTH, TUSER_WIDTH, STRADDLING) m_env;
    int unsigned timeout;

    // ------------------------------------------------------------------------
    // Functions
    // Constrctor of the test object
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Build phase function, e.g. the creation of test's internal objects
    function void build_phase(uvm_phase phase);
        // Initializing the reference to the environment
        m_env = uvm_ptc_mfb2pcie_axi::env #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, DATA_WIDTH, TUSER_WIDTH, STRADDLING)::type_id::create("m_env", this);
    endfunction

    virtual task tx_seq(uvm_phase phase);

        // Declaring the sequence library reference and initializing it
        uvm_axi::sequence_lib_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS) axi_seq;
        axi_seq = uvm_axi::sequence_lib_tx #(DATA_WIDTH, TUSER_WIDTH, REGIONS)::type_id::create("axi_tx_seq", this);

        axi_seq.init_sequence();
        axi_seq.min_random_count = 10;
        axi_seq.max_random_count = 20;

        //RUN TX Sequencer
        forever begin
            axi_seq.randomize();
            axi_seq.start(m_env.m_env_tx.m_sequencer);
        end

    endtask

    // ------------------------------------------------------------------------
    // Create environment and Run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);
        virt_sequence#(ITEM_WIDTH) m_vseq;

        phase.raise_objection(this);

        //RUN MFB TX SEQUENCE
        fork
            tx_seq(phase);
        join_none

        //RUN MFB RX SEQUENCE
        m_vseq = virt_sequence#(ITEM_WIDTH)::type_id::create("m_vseq");
        m_vseq.randomize();
        m_vseq.start(m_env.vscr);

        timeout = 1;
        fork
            test_wait_timeout(10);
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
