// test_speed.sv: Verification speed test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class test_speed #(int unsigned RX_ITEMS, int unsigned TX_ITEMS, int unsigned ITEM_WIDTH) extends test_base #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH);
    typedef uvm_component_registry #(test::test_speed #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH), "test::test_speed") type_id;

    // Constructor
    function new(string name = "test_speed", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        uvm_logic_vector_mvb::sequence_lib_rx #(RX_ITEMS, ITEM_WIDTH)::type_id::set_inst_override(
            uvm_logic_vector_mvb::sequence_lib_speed_rx #(RX_ITEMS, ITEM_WIDTH)::get_type(),
            "m_env.m_env_rx_mvb.mvb_seq",
            this
        );

        virtual_sequence_base #(TX_ITEMS, ITEM_WIDTH)::type_id::set_inst_override(
            virtual_sequence_speed #(TX_ITEMS, ITEM_WIDTH)::get_type(),
            "m_virtual_sequence",
            this
        );

        super.build_phase(phase);
    endfunction

endclass
