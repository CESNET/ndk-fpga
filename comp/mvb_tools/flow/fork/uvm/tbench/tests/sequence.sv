// sequence.sv: Virtual sequence
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(ITEM_WIDTH, OUTPUT_PORTS) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(ITEM_WIDTH, OUTPUT_PORTS))
    `uvm_declare_p_sequencer(uvm_mvb_fork::virt_sequencer#(ITEM_WIDTH, OUTPUT_PORTS))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                      m_reset;
    uvm_logic_vector::sequence_simple#(ITEM_WIDTH) m_logic_vector_sq;

    virtual function void init();

        m_reset           = uvm_reset::sequence_start::type_id::create("m_reset");
        m_logic_vector_sq = uvm_logic_vector::sequence_simple#(ITEM_WIDTH)::type_id::create("m_logic_vector_sq");

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

        #(10ns)

        for (int unsigned it = 0; it < REPEAT; it++) begin
            run_data();
        end

    endtask

    virtual task run_data();
        m_logic_vector_sq.randomize();
        m_logic_vector_sq.start(p_sequencer.m_logic_vector_scr);
    endtask

endclass
