// sequence.sv: Virtual sequence
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence)
    `uvm_declare_p_sequencer(uvm_cq_mfb2axi::sequencer)

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_pcie::sequence_request_lib m_cq_seq;

    virtual function void init();

        m_cq_seq = uvm_pcie::sequence_request_lib::type_id::create("m_cq_seq");

        m_cq_seq.init_sequence();
        m_cq_seq.min_random_count = 50;
        m_cq_seq.max_random_count = 100;
    endfunction

    task body();

        init();

        for (int unsigned it = 0; it < 15; it++) begin
            assert(m_cq_seq.randomize());
            m_cq_seq.start(p_sequencer.m_cq);
        end
    endtask

endclass
