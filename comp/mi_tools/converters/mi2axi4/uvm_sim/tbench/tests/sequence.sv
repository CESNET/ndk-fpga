// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH, CLK_PERIOD) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH, CLK_PERIOD))
    `uvm_declare_p_sequencer(uvm_mi2axi4lite::virt_sequencer#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                                                  m_reset_sq;
    uvm_mi2axi4lite::sequence_mi#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH, CLK_PERIOD) m_mi_sq;
    uvm_phase phase;

    virtual function void init(uvm_phase phase);

        m_reset_sq    = uvm_reset::sequence_start::type_id::create("m_reset_sq");
        m_mi_sq       = uvm_mi2axi4lite::sequence_mi#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH, CLK_PERIOD)::type_id::create("m_mi_sq");

        this.phase = phase;

    endfunction

    virtual task run_reset();
        m_reset_sq.randomize();
        m_reset_sq.start(p_sequencer.m_reset_sqr);
    endtask

    task body();

        fork
            run_reset();
        join_none

        #(200ns)

        fork
            m_mi_sq.randomize();
            m_mi_sq.start(p_sequencer.m_mi_sqr);
        join

        #(100ns);

    endtask
endclass
