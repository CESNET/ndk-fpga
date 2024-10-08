// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEMS, MVB_ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEMS, MVB_ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_mvb2mfb::virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEM_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                    m_reset;

    uvm_logic_vector::sequence_simple#(MVB_ITEM_WIDTH) m_mvb_data_seq;

    uvm_sequence#(uvm_mfb::sequence_item#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)) m_mfb_rdy_seq;
    uvm_mfb::sequence_lib_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)              m_mfb_rdy_lib;

    uvm_phase phase;

    virtual function void init(uvm_phase phase);

        m_reset             = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        m_mvb_data_seq      = uvm_logic_vector::sequence_simple #(MVB_ITEM_WIDTH)::type_id::create("m_mvb_data_seq");
        m_mvb_data_seq.transaction_count_min = 5000;
        m_mvb_data_seq.transaction_count_max = 10000;


        m_mfb_rdy_lib       = uvm_mfb::sequence_lib_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_mfb_rdy_lib");
        m_mfb_rdy_lib.init_sequence();
        m_mfb_rdy_lib.min_random_count = 100;
        m_mfb_rdy_lib.max_random_count = 200;
        m_mfb_rdy_seq = m_mfb_rdy_lib;

        this.phase = phase;

    endfunction

    virtual task mfb_rdy_seq();
        //RUN TX Sequencer
        forever begin
            m_mfb_rdy_seq.randomize();
            m_mfb_rdy_seq.start(p_sequencer.m_mfb_rdy_sqr);
        end
    endtask

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset_sqr);
    endtask

    task body();

        fork
            run_reset();
        join_none

        #(100ns);

        //RUN MFB and MVB TX SEQUENCE
        fork
            mfb_rdy_seq();
        join_none

        fork
            begin
                m_mvb_data_seq.randomize();
                m_mvb_data_seq.start(p_sequencer.m_mvb_data_sqr);
            end
        join_any

    endtask

endclass
