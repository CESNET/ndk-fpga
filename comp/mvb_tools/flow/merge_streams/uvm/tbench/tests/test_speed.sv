// test_speed.sv: Verification speed test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class test_speed #(int unsigned MVB_ITEMS, int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends test_base #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS);
    typedef uvm_component_registry #(test::test_speed #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS), "test::test_speed") type_id;

    // Constructor
    function new(string name = "test_speed", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            uvm_logic_vector_mvb::sequence_lib_rx #(MVB_ITEMS, MVB_ITEM_WIDTH)::type_id::set_inst_override(
                uvm_logic_vector_mvb::sequence_lib_speed_rx #(MVB_ITEMS, MVB_ITEM_WIDTH)::get_type(),
                $sformatf("m_env.m_env_rx_mvb_%0d.mvb_seq", i),
                this
            );
        end

        uvm_mvb::sequence_lib_tx#(MVB_ITEMS, MVB_ITEM_WIDTH)::type_id::set_inst_override(
            uvm_mvb::sequence_lib_tx_speed #(MVB_ITEMS, MVB_ITEM_WIDTH)::get_type(),
            "m_env.m_env_tx_mvb.mvb_seq",
            this
        );

        super.build_phase(phase);
    endfunction

endclass
