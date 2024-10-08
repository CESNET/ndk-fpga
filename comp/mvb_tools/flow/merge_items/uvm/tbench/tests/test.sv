//-- test.sv: Verification test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    typedef uvm_component_registry #(test::ex_test, "test::ex_test") type_id;

    int unsigned timeout;

    // Declare the environment reference variable
    merge_items::env #(RX0_ITEMS, RX1_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) m_env;

    // ------------------------------------------------------------------------
    // Functions

    // Constructor of the test object
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
        m_env = merge_items::env #(RX0_ITEMS, RX1_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);

        virt_sequence #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) m_vseq;
        m_vseq = virt_sequence #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH)::type_id::create("m_vseq");

        phase.raise_objection(this);
        m_vseq.init(phase);

        // RUN MVB RX SEQUENCE
        m_vseq.randomize();
        m_vseq.start(m_env.vscr);

        timeout = 1;
        fork
            test_wait_timeout(1000);
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
