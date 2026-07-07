//-- test.sv: Verification test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author: Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class ex_test #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ) extends uvm_test;
    typedef uvm_component_registry#(test::ex_test #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ), "test::ex_test") type_id;

    bit timeout;
    uvm_histogramer::env #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ) m_env;

    // ------------------------------------------------------------------------
    // Functions
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        m_env = uvm_histogramer::env#(
            INPUT_WIDTH,
            BOX_WIDTH,
            BOX_CNT,
            READ_PRIOR,
            CLEAR_BY_READ,
            CLEAR_BY_RST,
            DEVICE,
            REQ_WIDTH,
            RESP_WIDTH,
            ADDR_WIDTH
        )::type_id::create("m_env", this);
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
        virt_sequence #(
            INPUT_WIDTH,
            BOX_WIDTH,
            BOX_CNT,
            READ_PRIOR,
            CLEAR_BY_READ,
            CLEAR_BY_RST,
            DEVICE,
            REQ_WIDTH,
            RESP_WIDTH,
            ADDR_WIDTH
        ) m_vseq;

        phase.raise_objection(this, "Start of rx sequence");

        m_vseq = virt_sequence#(
            INPUT_WIDTH,
            BOX_WIDTH,
            BOX_CNT,
            READ_PRIOR,
            CLEAR_BY_READ,
            CLEAR_BY_RST,
            DEVICE,
            REQ_WIDTH,
            RESP_WIDTH,
            ADDR_WIDTH
        )::type_id::create("m_vseq");

        assert(m_vseq.randomize());
        m_vseq.start(m_env.vscr);

        timeout = 1;
        fork
            test_wait_timeout(DEBUG_TIME);
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
            `uvm_error(this.get_full_name(),
                       "\n\t===================================================\n\tTIMEOUT SOME PACKET STUCK IN DESIGN\n\t===================================================\n\n"
                           );
        end
    endfunction
endclass
