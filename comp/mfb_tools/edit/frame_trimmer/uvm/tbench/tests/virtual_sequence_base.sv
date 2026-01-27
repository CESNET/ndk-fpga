// virtual_sequence_base.sv: Virtual base sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_base #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned PKT_MTU) extends uvm_sequence;
    `uvm_object_param_utils(test::virtual_sequence_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU))
    `uvm_declare_p_sequencer(uvm_mfb_frame_trimmer::virtual_sequencer #(ITEM_WIDTH, META_WIDTH, PKT_MTU))

    uvm_reset::sequence_start                                                            m_reset;
    uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH)                                   m_rx_mfb_data;
    trim_sequence_library    #(BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU)              m_rx_mfb_meta;

    function new(string name = "virtual_sequence_base");
        super.new(name);
    endfunction

    virtual function void init();
        uvm_common::sequence_cfg_transactions m_rx_mfb_data_config;

        // Create the reset sequence
        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        // --------------- //
        // RX MFB sequence //
        // --------------- //

        // Create the RX MFB data sequence
        m_rx_mfb_data = uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH)::type_id::create("m_rx_mfb_data");
        // Configure the RX MFB data sequence
        m_rx_mfb_data.init_sequence();
        m_rx_mfb_data.cfg = new();
        m_rx_mfb_data.cfg.array_size_set(64, PKT_MTU);
        m_rx_mfb_data.min_random_count = 100;
        m_rx_mfb_data.max_random_count = 150;

        // Create the RX MFB data state config
        m_rx_mfb_data_config = new("m_rx_mfb_data_config");
        m_rx_mfb_data_config.transactions_min = 1200;
        m_rx_mfb_data_config.transactions_max = 1500;
        assert(m_rx_mfb_data_config.randomize());
        uvm_config_db #(uvm_common::sequence_cfg)::set(p_sequencer.m_rx_mfb_data, "", "state", m_rx_mfb_data_config);

        // Create the RX MFB meta sequence
        m_rx_mfb_meta = trim_sequence_library #(BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, PKT_MTU)::type_id::create("m_rx_mfb_meta");
        // Configure the RX MFB meta sequence
        m_rx_mfb_meta.init_sequence();
        m_rx_mfb_meta.min_random_count = 15;
        m_rx_mfb_meta.max_random_count = 25;
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

        // Run the RX MFB meta sequence
        fork
            forever begin
                assert(m_rx_mfb_meta.randomize());
                m_rx_mfb_meta.start(p_sequencer.m_rx_mfb_meta);
            end
        join_none

        // Run the RX MFB data sequence
        begin
            assert(m_rx_mfb_data.randomize());
            m_rx_mfb_data.start(p_sequencer.m_rx_mfb_data);
        end
    endtask

endclass
