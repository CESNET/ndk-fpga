// test.sv: Verification test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class ex_test extends uvm_test;
    typedef uvm_component_registry #(test::ex_test, "test::ex_test") type_id;

    // Declare the environment reference variable
    uvm_fifox::env #(DATA_WIDTH, STATUS_WIDTH, ITEMS_ACTUAL, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET) m_env;

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

    task test_wait_result(time time_length);
        time start_time = $time();
        while ($time()-start_time < time_length && m_env.sc.used() !== 0) #(600ns);
    endtask

    // Build phase function, e.g. the creation of test's internal objects
    function void build_phase(uvm_phase phase);
        m_env = uvm_fifox::env #(DATA_WIDTH, STATUS_WIDTH, ITEMS_ACTUAL, ALMOST_FULL_OFFSET, ALMOST_EMPTY_OFFSET)::type_id::create("m_env", this);
    endfunction

    // ------------------------------------------------------------------------
    // Create environment and run sequences on their sequencers
    virtual task run_phase(uvm_phase phase);

        virt_sequence #(DATA_WIDTH, MIN_TRANSACTION_COUNT, MAX_TRANSACTION_COUNT) m_vseq;
        m_vseq = virt_sequence #(DATA_WIDTH, MIN_TRANSACTION_COUNT, MAX_TRANSACTION_COUNT)::type_id::create("m_vseq");

        phase.raise_objection(this);
        m_vseq.init(phase);

        // RUN SEQUENCES
        m_vseq.randomize();
        m_vseq.start(m_env.vscr);

        test_wait_result(1000us);

        phase.drop_objection(this);

    endtask

    function void report_phase(uvm_phase phase);
        `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
    endfunction

endclass
