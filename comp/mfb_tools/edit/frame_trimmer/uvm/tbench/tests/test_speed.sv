// test_speed.sv: Verification speed test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class test_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH) extends test_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH);
    typedef uvm_component_registry #(test::test_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH), "test::test_speed") type_id;

    // Constructor
    function new(string name = "test_speed", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        uvm_logic_vector_array_mfb::sequence_lib_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH+1+LEN_WIDTH)::type_id::set_inst_override(
            uvm_logic_vector_array_mfb::sequence_lib_rx_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH+1+LEN_WIDTH)::get_type(),
            "m_env.m_env_rx_mfb.mfb_seq",
            this
        );

        virtual_sequence_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH)::type_id::set_inst_override(
            virtual_sequence_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH)::get_type(),
            "m_virtual_sequence",
            this
        );

        super.build_phase(phase);
    endfunction

endclass
