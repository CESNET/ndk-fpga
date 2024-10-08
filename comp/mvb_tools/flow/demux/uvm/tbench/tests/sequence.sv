// sequence.sv: Virtual sequence
// Copyright (C) 2023-2024 CESNET z. s. p. o.
// Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(ITEM_WIDTH, TX_PORTS) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(ITEM_WIDTH, TX_PORTS))
    `uvm_declare_p_sequencer(uvm_mvb_demux::virt_sequencer#(ITEM_WIDTH, TX_PORTS))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                                          m_reset_seq;
    uvm_logic_vector::sequence_simple#(ITEM_WIDTH + $clog2(TX_PORTS))  m_logic_vector_seq;

    virtual function void init();
        m_reset_seq        = uvm_reset::sequence_start::type_id::create("m_reset_seq");

        m_logic_vector_seq = uvm_logic_vector::sequence_simple#(ITEM_WIDTH + $clog2(TX_PORTS))::type_id::create("m_logic_vector_seq");
        m_logic_vector_seq.transaction_count_min = 1000;
        m_logic_vector_seq.transaction_count_max = 3000;
    endfunction

    virtual task run_reset();
        m_reset_seq.randomize();
        m_reset_seq.start(p_sequencer.m_reset_sqcr);
    endtask

    virtual task run_mfb();
        m_logic_vector_seq.randomize();
        m_logic_vector_seq.start(p_sequencer.m_logic_vector_sqcr);
    endtask

    task body();
        init();

        fork
            run_reset();
        join_none

        #(100ns)

        repeat (RUNS) begin
            run_mfb();
        end
    endtask
endclass
