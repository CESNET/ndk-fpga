// test_base.sv: Verification base test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class test_base #(int unsigned MVB_ITEMS, int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends uvm_test;
    typedef uvm_component_registry #(test::test_base #(
        MVB_ITEMS,
        MVB_ITEM_WIDTH,
        RX_STREAMS
    ), "test::test_base") type_id;

    // Verification environment
    uvm_mvb_merge_streams::env #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) m_env;

    // Constructor
    function new(string name = "test_base", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m_env = uvm_mvb_merge_streams::env #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_env", this);
    endfunction

    task run_phase(uvm_phase phase);
        time end_time;
        virtual_sequence_base #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) m_virtual_sequence;


        m_virtual_sequence =
            virtual_sequence_base #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create("m_virtual_sequence", this);

        // Raise objection
        phase.raise_objection(this);

        // Run the virtual sequence
        m_virtual_sequence.init();
        assert(m_virtual_sequence.randomize());
        m_virtual_sequence.start(m_env.m_virtual_sequencer);

        #(2us);

        // Wait for the end of the transaction processing
        end_time = $time() + 200us;
        while(end_time > $time() && m_env.m_scoreboard.used()) begin
            #(600ns);
            `uvm_info(get_full_name(), "\n\tWaiting for the transactions to be processed.", UVM_MEDIUM);
        end

        // Drop objection
        phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);

        `uvm_info(get_full_name(), $sformatf("\n\tTEST %s ENDED\n", get_type_name()), UVM_NONE);
    endfunction

    static function type_id get_type();
        return type_id::get();
    endfunction

    function string get_type_name();
        return get_type().get_type_name();
    endfunction

endclass
