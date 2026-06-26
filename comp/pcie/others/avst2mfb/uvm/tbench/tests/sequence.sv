// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH))
    `uvm_declare_p_sequencer(uvm_pcie_avst2mfb::virt_sequencer#(MFB_ITEM_WIDTH, META_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                                                                           m_reset;
    uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)                                               m_logic_vector_array_sq_lib;
    uvm_logic_vector::sequence_endless#(META_WIDTH)                                        m_meta_sq;

    virtual function void init();

        m_reset                     = uvm_reset::sequence_start::type_id::create("m_reset");
        m_logic_vector_array_sq_lib = uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)::type_id::create("m_logic_vector_array_sq_lib");
        m_meta_sq                   = uvm_logic_vector::sequence_endless#(META_WIDTH)::type_id::create("m_meta_sq");

        m_logic_vector_array_sq_lib.init_sequence();
        m_logic_vector_array_sq_lib.min_random_count = 50;
        m_logic_vector_array_sq_lib.max_random_count = 100;
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
            run_avalon_data();
            forever begin
                m_meta_sq.randomize();
                m_meta_sq.start(p_sequencer.m_logic_vector_scr);
            end
        join_any

    endtask

    virtual task run_avalon_data();
        for (int unsigned it = 0; it < 3; it++) begin
            assert(m_logic_vector_array_sq_lib.randomize());
            m_logic_vector_array_sq_lib.start(p_sequencer.m_logic_vector_array_scr);
        end
    endtask

endclass
