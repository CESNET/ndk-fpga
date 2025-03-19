// virtual_sequence_speed.sv: Virtual speed sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_speed #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned PKT_MTU, int unsigned USERMETA_WIDTH, int unsigned RX_MVB_ITEM_WIDTH) extends virtual_sequence_base #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH);
    `uvm_object_param_utils(test::virtual_sequence_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, PKT_MTU, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_mfb_frame_extender::virtual_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH, RX_MVB_ITEM_WIDTH))

    uvm_mfb::sequence_lib_tx_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH) m_tx_mfb;
    uvm_mvb::sequence_lib_tx_speed #(MFB_REGIONS, USERMETA_WIDTH)                                                  m_tx_mvb;

    function new(string name = "virtual_sequence_speed");
        super.new(name);
    endfunction

    function void init();
        super.init();

        // --------------- //
        // TX MFB sequence //
        // --------------- //

        // Create the TX MFB sequence
        m_tx_mfb = uvm_mfb::sequence_lib_tx_speed #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, USERMETA_WIDTH)::type_id::create("m_tx_mfb");
        // Configure the TX MFB sequence
        m_tx_mfb.init_sequence();
        m_tx_mfb.min_random_count = 150;
        m_tx_mfb.max_random_count = 200;

        // --------------- //
        // TX MVB sequence //
        // --------------- //

        // Create the TX MVB sequence
        m_tx_mvb = uvm_mvb::sequence_lib_tx_speed #(MFB_REGIONS, USERMETA_WIDTH)::type_id::create("m_tx_mvb");
        // Configure the TX MVB sequence
        m_tx_mvb.init_sequence();
        m_tx_mvb.min_random_count = 150;
        m_tx_mvb.max_random_count = 200;
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

        fork
            // Run the TX MFB sequence
            forever begin
                assert(m_tx_mfb.randomize());
                m_tx_mfb.start(p_sequencer.m_tx_mfb);
            end
            // Run the TX MVB sequence
            forever begin
                assert(m_tx_mvb.randomize());
                m_tx_mvb.start(p_sequencer.m_tx_mvb);
            end
        join_none

        // Run the RX MVB sequence
        fork
            forever begin
                assert(m_rx_mvb.randomize());
                m_rx_mvb.start(p_sequencer.m_rx_mvb);
            end
        join_none

        // Run the RX MFB sequence
        begin
            assert(m_rx_mfb.randomize());
            m_rx_mfb.start(p_sequencer.m_rx_mfb);
        end

        // Wait for all frames to be processed
        wait(p_sequencer.m_rx_mfb.frame_lengths.num() == 0);
    endtask

endclass
