// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(RX0_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH))
    `uvm_declare_p_sequencer(merge_items::virt_sequencer #(RX0_ITEM_WIDTH, RX1_ITEM_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start m_reset;

    int unsigned transaction_count;
    single_transaction_sequence #(RX0_ITEM_WIDTH) m_mvb_data0_sq;
    single_transaction_sequence #(RX1_ITEM_WIDTH) m_mvb_data1_sq;

    uvm_phase phase;

    virtual function void init(uvm_phase phase);

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        randomize(transaction_count) with {
            transaction_count >= 2000;
            transaction_count <= 6000;
        };
        m_mvb_data0_sq = single_transaction_sequence #(RX0_ITEM_WIDTH)::type_id::create("m_mvb_data0_sq");
        m_mvb_data1_sq = single_transaction_sequence #(RX1_ITEM_WIDTH)::type_id::create("m_mvb_data1_sq");

        this.phase = phase;

    endfunction

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);

    endtask

    task body();

        fork
            run_reset();
        join_none

        #(100ns);

        fork
            repeat(transaction_count) begin
                begin
                    m_mvb_data0_sq.start(p_sequencer.m_mvb_data0_sqr);
                end
                begin
                    m_mvb_data1_sq.start(p_sequencer.m_mvb_data1_sqr);
                end
            end
        join_any

    endtask

endclass
