// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequence#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) extends uvm_sequence;

    `uvm_object_param_utils(test::virt_sequence#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))
    `uvm_declare_p_sequencer(uvm_mfb_pipe::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                          m_reset;
    uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH) m_mfb_data_sq;
    uvm_logic_vector::sequence_endless #(META_WIDTH)   m_mfb_meta_sq;

    virtual function void init();

        m_reset       = uvm_reset::sequence_start::type_id::create("m_reset");
        m_mfb_data_sq = uvm_logic_vector_array::sequence_lib #(ITEM_WIDTH)::type_id::create("m_mfb_data_sq");
        m_mfb_meta_sq = uvm_logic_vector::sequence_endless #(META_WIDTH)::type_id::create("m_mfb_meta_sq");

        m_mfb_data_sq.init_sequence();
        m_mfb_data_sq.min_random_count = 4;
        m_mfb_data_sq.max_random_count = 10;

    endfunction

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);
    endtask

    task body();

        init();

        fork
            run_reset();
        join_none

        #(100ns);

        fork
            begin
                m_mfb_data_sq.randomize();
                m_mfb_data_sq.start(p_sequencer.m_mfb_data_sqr);
            end
            begin
                m_mfb_meta_sq.randomize();
                m_mfb_meta_sq.start(p_sequencer.m_mfb_meta_sqr);
            end
        join_any
    endtask

endclass


