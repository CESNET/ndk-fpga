// test_speed.sv: Verification speed test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class test_speed #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned PKT_MTU, int unsigned USERMETA_WIDTH, int unsigned RX_MVB_ITEM_WIDTH) extends test_base #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH);
    typedef uvm_component_registry #(test::test_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH), "test::test_speed") type_id;

    // Constructor
    function new(string name = "test_speed", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        // ------------------- //
        // Database overriding //
        // ------------------- //

        uvm_logic_vector_array_mfb::sequence_lib_rx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::type_id::set_inst_override(
            uvm_logic_vector_array_mfb::sequence_lib_rx_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, 0)::get_type(),
            "m_env.m_env_rx_mfb.mfb_seq",
            this
        );

        uvm_logic_vector_mvb::sequence_lib_rx #(MFB_REGIONS, RX_MVB_ITEM_WIDTH)::type_id::set_inst_override(
            uvm_logic_vector_mvb::sequence_lib_speed_rx #(MFB_REGIONS, RX_MVB_ITEM_WIDTH)::get_type(),
            "m_env.m_env_rx_mvb.mvb_seq",
            this
        );


        uvm_mfb::sequence_lib_tx #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH)::type_id::set_inst_override(
            uvm_mfb::sequence_lib_tx_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH)::get_type(),
            "m_env.m_env_tx_mfb.mfb_seq",
            this
        );

        uvm_mvb::sequence_lib_tx #(MFB_REGIONS, USERMETA_WIDTH)::type_id::set_inst_override(
            uvm_mvb::sequence_lib_tx_speed #(MFB_REGIONS, USERMETA_WIDTH)::get_type(),
            "m_env.m_env_tx_mvb.mvb_seq",
            this
        );


        super.build_phase(phase);
    endfunction

endclass
