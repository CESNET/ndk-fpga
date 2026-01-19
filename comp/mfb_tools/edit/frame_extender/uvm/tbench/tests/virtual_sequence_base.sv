// virtual_sequence_base.sv: Virtual base sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_base #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned PKT_MTU, int unsigned USERMETA_WIDTH, int unsigned RX_MVB_ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virtual_sequence_base #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_mfb_frame_extender::virtual_sequencer #(MFB_ITEM_WIDTH, RX_MVB_ITEM_WIDTH))

    uvm_reset::sequence_start                                                                                            m_reset;
    uvm_logic_vector_array::sequence_lib #(MFB_ITEM_WIDTH)                                                               m_rx_mfb;
    extension_sequence_library           #(MFB_BLOCK_SIZE, PKT_MTU, RX_MVB_ITEM_WIDTH)                                   m_rx_mvb;

    function new(string name = "virtual_sequence_base");
        super.new(name);
    endfunction

    virtual function void init();
        uvm_common::sequence_cfg_transactions m_rx_mfb_config;

        // Create the reset sequence
        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        // --------------- //
        // RX MFB sequence //
        // --------------- //

        // Create the RX MFB sequence
        m_rx_mfb = uvm_logic_vector_array::sequence_lib #(MFB_ITEM_WIDTH)::type_id::create("m_rx_mfb");
        // Configure the RX MFB sequence
        m_rx_mfb.init_sequence();
        m_rx_mfb.cfg = new();
        m_rx_mfb.cfg.array_size_set(64, PKT_MTU);
        m_rx_mfb.min_random_count = 30;
        m_rx_mfb.max_random_count = 50;

        // --------------- //
        // RX MVB sequence //
        // --------------- //

        // Create the RX MVB sequence
        m_rx_mvb = extension_sequence_library #(MFB_BLOCK_SIZE, PKT_MTU, RX_MVB_ITEM_WIDTH)::type_id::create("m_rx_mvb");
        // Configure the RX MVB sequence
        m_rx_mvb.init_sequence();
        m_rx_mvb.min_random_count = 150;
        m_rx_mvb.max_random_count = 200;
    endfunction

    task body();
        init();

        // Run the reset sequence
        fork
            begin
                assert(m_reset.randomize());
                m_reset.start(p_sequencer.m_reset);
            end
        join_none

        #(100ns);

        // Run the RX MVB sequence
        fork
            forever begin
                assert(m_rx_mvb.randomize());
                m_rx_mvb.start(p_sequencer.m_rx_mvb);
            end
        join_none

        // Run the RX MFB sequence
        assert(m_rx_mfb.randomize());
        m_rx_mfb.start(p_sequencer.m_rx_mfb);

        // Wait for all frames to be processed
        wait(p_sequencer.m_rx_mfb.frame_lengths.num() == 0);
    endtask

endclass
