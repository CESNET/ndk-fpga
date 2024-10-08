// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))
    `uvm_declare_p_sequencer(uvm_items_valid::virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_header_type::sequence_lib #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) m_info_lib;

    virtual function void init();

        m_info_lib = uvm_header_type::sequence_lib #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH)::type_id::create("m_info_lib");

        m_info_lib.init_sequence();
        m_info_lib.min_random_count = 100;
        m_info_lib.max_random_count = 200;
        m_info_lib.randomize();

    endfunction

    task body();

        init();

        m_info_lib.start(p_sequencer.m_info);
    endtask

endclass
