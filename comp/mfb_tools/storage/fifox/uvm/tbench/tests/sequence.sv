// sequence.sv: Virtual sequence
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Mikuláš Brázda <xbrazd21@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence extends uvm_sequence;
    `uvm_object_utils(test::virt_sequence)
    `uvm_declare_p_sequencer(uvm_mfb_fifox::virt_sequencer#(ITEM_WIDTH, META_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start       m_reset;
    uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)    m_byte_array_sq_lib;
    uvm_logic_vector::sequence_endless#(META_WIDTH)  m_logic_vector_sq_endless;

    virtual function void init();

        m_reset      = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        m_byte_array_sq_lib   = uvm_logic_vector_array::sequence_lib#(ITEM_WIDTH)::type_id::create("m_byte_array_seq_lib");

        m_byte_array_sq_lib.init_sequence();
        m_byte_array_sq_lib.min_random_count   = 60;
        m_byte_array_sq_lib.max_random_count   = 80;

        m_logic_vector_sq_endless = uvm_logic_vector::sequence_endless#(META_WIDTH)::type_id::create("m_logic_vector_sq_endless");

    endfunction

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);

    endtask

    task body();

        init();

        fork
            run_meta();
            run_reset();
        join_none

        fork
            run_mfb();
        join



    endtask

    virtual task run_meta();
        #(100ns);
        m_logic_vector_sq_endless.randomize();
        m_logic_vector_sq_endless.start(p_sequencer.m_mfb_byte_array_scr.m_meta);
    endtask

    virtual task run_mfb();
        #(100ns);
        m_byte_array_sq_lib.randomize();
        m_byte_array_sq_lib.start(p_sequencer.m_mfb_byte_array_scr.m_data);
    endtask

endclass
