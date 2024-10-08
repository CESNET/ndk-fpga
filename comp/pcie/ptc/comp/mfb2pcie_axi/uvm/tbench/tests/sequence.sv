// sequence.sv: Virtual sequence
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_ptc_mfb2pcie_axi::virt_sequencer#(ITEM_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                 m_reset;
    uvm_logic_vector_array::sequence_lib#(32) m_logic_vector_array_sq_lib;

    virtual function void init();

        m_reset      = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        m_logic_vector_array_sq_lib   = uvm_logic_vector_array::sequence_lib#(32)::type_id::create("m_logic_vector_array_seq_lib");

        m_logic_vector_array_sq_lib.init_sequence();
        m_logic_vector_array_sq_lib.cfg = new();
        m_logic_vector_array_sq_lib.cfg.array_size_set(2, 1500);
        m_logic_vector_array_sq_lib.min_random_count = 60;
        m_logic_vector_array_sq_lib.max_random_count = 80;

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

        #(10ns);

        run_mfb();

    endtask

    virtual task run_mfb();
        m_logic_vector_array_sq_lib.randomize();
        m_logic_vector_array_sq_lib.start(p_sequencer.m_byte_array_scr);
    endtask

endclass
