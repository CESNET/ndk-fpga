//-- sequence.sv: Virtual sequence
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class virt_seq #(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE) extends uvm_sequence;

    `uvm_object_utils(test::virt_seq #(MRRS, MIN_READ_REQ_SIZE, MPS, MIN_WRITE_REQ_SIZE))
    `uvm_declare_p_sequencer(uvm_dma_up::sequencer);

    function new (string name = "virt_seq");
        super.new(name);
    endfunction

    uvm_ptc_info::sequence_lib_info #(MRRS, MIN_READ_REQ_SIZE) m_info_lib;
    uvm_sequence#(uvm_ptc_info::sequence_item)                 m_info;
    //uvm_reset::sequence_reset     m_reset;
    uvm_logic_vector_array::sequence_lib#(32)  m_packet;

    virtual function void init();
        //m_reset = uvm_reset::sequence_reset::type_id::create("rst_seq");

        m_packet = uvm_logic_vector_array::sequence_lib#(32)::type_id::create("m_packet");
        m_packet.init_sequence();
        m_packet.cfg = new();
        m_packet.cfg.array_size_set(MIN_WRITE_REQ_SIZE, MPS);
        m_packet.min_random_count = 60;
        m_packet.max_random_count = 80;

        m_info_lib   = uvm_ptc_info::sequence_lib_info #(MRRS, MIN_READ_REQ_SIZE)::type_id::create("m_info_lib");
        m_info_lib.init_sequence();
        m_info_lib.min_random_count = 60;
        m_info_lib.max_random_count = 80;
        m_info = m_info_lib;
    endfunction

    //virtual task run_reset();
    //    m_reset.randomize();
    //    m_reset.start(p_sequencer.m_reset);
    //endtask

    function void pre_randomize();
        init();
        m_packet.randomize();
    endfunction

    task body();
        //fork
        //    run_reset();
        //join_none

        fork
            m_packet.start(p_sequencer.m_data);
            forever begin
                assert(m_info.randomize());
                m_info.start(p_sequencer.m_info);
            end
        join_any
    endtask
endclass
