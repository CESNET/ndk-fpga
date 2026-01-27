// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, FRAME_SIZE_MIN, FRAME_SIZE_MAX) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, FRAME_SIZE_MIN, FRAME_SIZE_MAX))
    `uvm_declare_p_sequencer(uvm_rx_mac_lite_buffer::virt_sequencer #(MFB_ITEM_WIDTH, MFB_META_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                              m_reset_rx;
    uvm_reset::sequence_start                              m_reset_tx;

    uvm_logic_vector_array::sequence_lib #(MFB_ITEM_WIDTH) m_mfb_data_sq_lib;
    uvm_logic_vector::sequence_endless #(MFB_META_WIDTH)   m_mfb_meta_sq;

    uvm_phase phase;

    virtual function void init(uvm_phase phase);
        uvm_logic_vector_array::config_sequence mfb_cfg;

        //RESET
        m_reset_rx          = uvm_reset::sequence_start::type_id::create("m_reset_rx_seq", p_sequencer);
        m_reset_tx          = uvm_reset::sequence_start::type_id::create("m_reset_tx_seq", p_sequencer);

        //RX
        m_mfb_data_sq_lib   = uvm_logic_vector_array::sequence_lib #(MFB_ITEM_WIDTH)::type_id::create("m_mfb_data_sq_lib", p_sequencer);
        m_mfb_meta_sq       = uvm_logic_vector::sequence_endless #(MFB_META_WIDTH)::type_id::create("m_mfb_meta_sq", p_sequencer);

        mfb_cfg = new();
        mfb_cfg.array_size_set(FRAME_SIZE_MIN, FRAME_SIZE_MAX);
        m_mfb_data_sq_lib.init_sequence(mfb_cfg);
        m_mfb_data_sq_lib.min_random_count = 150;
        m_mfb_data_sq_lib.max_random_count = 300;

        this.phase = phase;
    endfunction

    virtual task run_reset_rx();
        m_reset_rx.randomize();
        m_reset_rx.start(p_sequencer.m_reset_rx_sqr);
    endtask

    virtual task run_reset_tx();
        m_reset_tx.randomize();
        m_reset_tx.start(p_sequencer.m_reset_tx_sqr);
    endtask

    task body();

        fork
            run_reset_rx();
            run_reset_tx();
        join_none

        #(100ns);

        fork
            begin
                m_mfb_data_sq_lib.randomize();
                m_mfb_data_sq_lib.start(p_sequencer.m_mfb_data_sqr);
            end
            begin
                m_mfb_meta_sq.randomize();
                m_mfb_meta_sq.start(p_sequencer.m_mfb_meta_sqr);
            end
        join_any

    endtask

endclass
