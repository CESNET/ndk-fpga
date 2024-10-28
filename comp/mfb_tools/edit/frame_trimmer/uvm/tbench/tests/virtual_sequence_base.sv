// virtual_sequence_base.sv: Virtual base sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_base #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned LEN_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virtual_sequence_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH))
    `uvm_declare_p_sequencer(uvm_mfb_frame_trimmer::virtual_sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH))

    uvm_reset::sequence_start                                                            m_reset;
    uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH)                                   m_rx_mfb_data;
    trim_sequence_library    #(BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH)            m_rx_mfb_meta;
    uvm_mfb::sequence_lib_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_tx_mfb;

    function new(string name = "virtual_sequence_base");
        super.new(name);
    endfunction

    virtual function void init();
        uvm_logic_vector_array::config_sequence m_rx_mfb_data_config;

        // Create the reset sequence
        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        // ---------------- //
        // RX MFB sequences //
        // ---------------- //

        // Create the RX MFB data sequence
        m_rx_mfb_data = uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH)::type_id::create("m_rx_mfb_data");
        // Configure the RX MFB data sequence
        m_rx_mfb_data_config = new();
        m_rx_mfb_data_config.array_size_min = 64;
        m_rx_mfb_data_config.array_size_max = 3000;
        m_rx_mfb_data.init_sequence(m_rx_mfb_data_config);
        m_rx_mfb_data.min_random_count = 15;
        m_rx_mfb_data.max_random_count = 25;

        // Create the RX MFB meta sequence
        m_rx_mfb_meta = trim_sequence_library #(BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH)::type_id::create("m_rx_mfb_meta");
        // Configure the RX MFB meta sequence
        m_rx_mfb_meta.init_sequence();
        m_rx_mfb_meta.min_random_count = 15;
        m_rx_mfb_meta.max_random_count = 25;

        // --------------- //
        // TX MFB sequence //
        // --------------- //

        // Create the TX MFB sequence
        m_tx_mfb = uvm_mfb::sequence_lib_tx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_tx_mfb");
        // Configure the TX MFB sequence
        m_tx_mfb.init_sequence();
        m_tx_mfb.min_random_count = 150;
        m_tx_mfb.max_random_count = 200;
    endfunction

    task body();
        // Run the reset sequence
        fork
            begin
                assert(m_reset.randomize());
                m_reset.start(p_sequencer.m_reset);
            end
        join_none

        #(100ns);

        // Run the TX MFB sequence
        fork
            forever begin
                assert(m_tx_mfb.randomize());
                m_tx_mfb.start(p_sequencer.m_tx_mfb);
            end
        join_none

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
