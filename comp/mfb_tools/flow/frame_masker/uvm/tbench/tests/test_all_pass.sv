// test_all_pass.sv: Test with masking off
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class test_all_pass extends ex_test;
    typedef uvm_component_registry #(test::test_all_pass, "test::test_all_pass") type_id;

    // Constructor
    function new(string name = "test_all_pass", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        uvm_logic_vector::sequence_endless #(MFB_REGIONS)::type_id::set_inst_override(
            sequence_all_pass #(MFB_REGIONS)::get_type(),
            "m_env.vscr.m_mvb_data_seq",
            this
        );

        super.build_phase(phase);
    endfunction

    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);

        // It doesn't make sense in this test
        m_env.m_coverage_model.discard_covergroup.option.weight      = 0;
        m_env.m_coverage_model.discard_covergroup.type_option.weight = 0;
    endfunction

endclass
