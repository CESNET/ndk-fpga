// sequence.sv: Virtual sequence
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence #(MIN_SIZE, PKT_MTU, DATA_SIZE_MAX, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, HEADER_SIZE, MVB_ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(MIN_SIZE, PKT_MTU, DATA_SIZE_MAX, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, HEADER_SIZE, MVB_ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_superunpacketer::virt_sequencer #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, HEADER_SIZE, MVB_ITEM_WIDTH, HEADER_SIZE))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                                                                                                        m_reset;
    uvm_logic_vector_array::sequence_lib #(MFB_ITEM_WIDTH)                                                                           m_byte_array_sq_lib;
    uvm_superpacket_header::sequence_simple #(MVB_ITEM_WIDTH, HEADER_SIZE)                                                           m_info;
    uvm_superpacket_size::sequence_lib#(MIN_SIZE, PKT_MTU)                                                                           m_size_sq_lib;
    uvm_phase phase;

    virtual function void init(uvm_phase phase);

        m_reset             = uvm_reset::sequence_start::type_id::create("m_reset_seq");
        m_byte_array_sq_lib = uvm_logic_vector_array::sequence_lib #(MFB_ITEM_WIDTH)::type_id::create("m_byte_array_seq_lib");
        m_info              = uvm_superpacket_header::sequence_simple#(MVB_ITEM_WIDTH, HEADER_SIZE)::type_id::create("m_info");
        m_size_sq_lib       = uvm_superpacket_size::sequence_lib#(MIN_SIZE, PKT_MTU)::type_id::create("m_size_seq_lib");

        m_byte_array_sq_lib.init_sequence();
        m_byte_array_sq_lib.cfg = new();
        m_byte_array_sq_lib.cfg.array_size_set(64, DATA_SIZE_MAX);
        m_byte_array_sq_lib.min_random_count = 100;
        m_byte_array_sq_lib.max_random_count = 200;
        m_byte_array_sq_lib.randomize();

        m_size_sq_lib.init_sequence();
        m_size_sq_lib.min_random_count = 100;
        m_size_sq_lib.max_random_count = 200;
        m_size_sq_lib.randomize();

        this.phase = phase;
    endfunction


    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);
    endtask

    task body();

        p_sequencer.m_info.set_report_verbosity_level(UVM_NONE);
        p_sequencer.m_size.set_report_verbosity_level(UVM_NONE);
        p_sequencer.m_byte_array_scr.set_report_verbosity_level(UVM_NONE);

        fork
            run_reset();
        join_none

        #(100ns);

        //RUN MFB and MVB TX SEQUENCE
        fork
            m_byte_array_sq_lib.start(p_sequencer.m_byte_array_scr);
            forever begin
                m_info.randomize();
                m_info.start(p_sequencer.m_info);
            end
            forever begin
                m_size_sq_lib.start(p_sequencer.m_size);
            end
        join_any

    endtask

endclass
