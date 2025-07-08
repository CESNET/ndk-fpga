// test_all_pass_and_one_frame.sv: Test with masking off and maximum one frame per MFB word
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class test_all_pass_and_one_frame extends test_all_pass;
    typedef uvm_component_registry #(test::test_all_pass_and_one_frame, "test::test_all_pass_and_one_frame") type_id;

    function new(string name = "test_all_pass_and_one_frame", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        uvm_logic_vector_array_mfb::sequence_lib_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::set_inst_override(
            sequence_lib_one_frame #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::get_type(),
            "m_env.m_env_rx.mfb_seq",
            this
        );

        super.build_phase(phase);
    endfunction

    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);

        // It doesn't make sense in this test
        m_env.m_coverage_model.frame_count_covergroup.option.weight      = 0;
        m_env.m_coverage_model.frame_count_covergroup.type_option.weight = 0;
    endfunction

endclass
