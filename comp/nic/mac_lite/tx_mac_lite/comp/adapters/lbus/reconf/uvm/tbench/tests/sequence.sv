// sequence.sv: Virtual sequence
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence)
    `uvm_declare_p_sequencer(uvm_mfb_to_lbus_adapter::virt_sequencer)

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start       m_reset;
    uvm_byte_array::sequence_lib    m_byte_array_sq_lib;

    virtual function void init();

        m_reset      = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        m_byte_array_sq_lib   = uvm_byte_array::sequence_lib::type_id::create("m_byte_array_seq_lib");

        m_byte_array_sq_lib.init_sequence();
        m_byte_array_sq_lib.min_random_count   = 200;
        m_byte_array_sq_lib.max_random_count   = 300;

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

        run_mfb();

    endtask

    virtual task run_mfb();
        m_byte_array_sq_lib.randomize();
        m_byte_array_sq_lib.start(p_sequencer.m_byte_array_scr);
    endtask

endclass
