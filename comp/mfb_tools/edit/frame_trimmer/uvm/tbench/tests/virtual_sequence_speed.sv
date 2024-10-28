// virtual_sequence_speed.sv: Virtual speed sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_speed #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH, int unsigned LEN_WIDTH) extends virtual_sequence_base #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH);
    `uvm_object_param_utils(test::virtual_sequence_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH))
    `uvm_declare_p_sequencer(uvm_mfb_frame_trimmer::virtual_sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH))

    uvm_mfb::sequence_lib_tx_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) m_tx_mfb;

    function new(string name = "virtual_sequence_speed");
        super.new(name);
    endfunction

    function void init();
        super.init();

        // --------------- //
        // TX MFB sequence //
        // --------------- //

        // Create the TX MFB sequence
        m_tx_mfb = uvm_mfb::sequence_lib_tx_speed #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::type_id::create("m_tx_mfb");
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
