// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(MFB_ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(MFB_ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_pcie_cc_mfb2axi::virt_sequencer#(MFB_ITEM_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH) m_rx;
    uvm_reset::sequence_start                             m_reset;

    virtual function void init();

        m_rx = uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)::type_id::create("m_rx", m_sequencer);
        m_rx.init_sequence();
        m_rx.min_random_count = 50;
        m_rx.max_random_count = 100;

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset", m_sequencer);
    endfunction

    task body();

        init();

        fork
            reset();
            run_axi_data();
        join_any

    endtask

    virtual task reset();
        for (int unsigned it = 0; it < 10; it++) begin
            m_reset.randomize();
            m_reset.start(p_sequencer.m_reset);
        end
    endtask

    virtual task run_axi_data();
        for (int unsigned it = 0; it < 10; it++) begin
            m_rx.randomize();
            m_rx.start(p_sequencer.m_logic_vector_array_scr);
        end
    endtask

endclass
