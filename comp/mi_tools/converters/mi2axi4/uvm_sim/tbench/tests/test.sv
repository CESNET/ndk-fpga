//-- test.sv: Verification test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    `uvm_component_utils(test::ex_test);

    bit timeout;
    uvm_mi2axi4lite::env #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH) m_env;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_mi2axi4lite::env #(MI_DATA_WIDTH, MI_ADDRESS_WIDTH)::type_id::create("m_env", this);
    endfunction

    task test_wait_timeout(int unsigned time_length);
        #(time_length*1us);
    endtask

    // ------------------------------------------------------------------------
    // Create environment and Run sequences o their sequencers
    task run_seq_rx(uvm_phase phase);
        virt_sequence#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH, CLK_PERIOD) m_vseq;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH, CLK_PERIOD)::type_id::create("m_vseq");
        m_vseq.init(phase);
        assert(m_vseq.randomize());
        m_vseq.start(m_env.vscr);

        phase.drop_objection(this, "End of rx sequence");
    endtask

    virtual task run_phase(uvm_phase phase);
        run_seq_rx(phase);
    endtask

endclass
