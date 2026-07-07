// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequence #(
    INPUT_WIDTH,
    BOX_WIDTH,
    BOX_CNT,
    READ_PRIOR,
    CLEAR_BY_READ,
    CLEAR_BY_RST,
    DEVICE,
    REQ_WIDTH,
    RESP_WIDTH,
    ADDR_WIDTH
) extends uvm_sequence;

    `uvm_object_param_utils(test::virt_sequence #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ))
    `uvm_declare_p_sequencer(uvm_histogramer::virt_sequencer #(
        INPUT_WIDTH,
        BOX_WIDTH,
        BOX_CNT,
        READ_PRIOR,
        CLEAR_BY_READ,
        CLEAR_BY_RST,
        DEVICE,
        REQ_WIDTH,
        RESP_WIDTH,
        ADDR_WIDTH
    ))

    uvm_reset::sequence_start                                                                   m_reset;
    test::sequence_read  #(REQ_WIDTH, INPUT_WIDTH, ADDR_WIDTH)                                  seq_read;
    test::sequence_rand  #(REQ_WIDTH, INPUT_WIDTH, ADDR_WIDTH, READ_OCCURENCE, WRITE_OCCURENCE) seq_rand;

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    virtual function void init();
        m_reset     = uvm_reset::sequence_start::type_id::create("m_reset");

        seq_read = test::sequence_read#(REQ_WIDTH, INPUT_WIDTH, ADDR_WIDTH)::type_id::create("seq_read");
        seq_rand  = test::sequence_rand#(
            REQ_WIDTH,
            INPUT_WIDTH,
            ADDR_WIDTH,
            READ_OCCURENCE,
            WRITE_OCCURENCE
        )::type_id::create("seq_rand");
    endfunction

    virtual task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);
    endtask

    task run_seq_read();
        seq_read.start(p_sequencer.req_sqr);
    endtask

    task run_seq_rand();
        for(int i = 0; i < RAND_SEQ_REPEATS; i++) begin
            seq_rand.randomize();
            seq_rand.start(p_sequencer.req_sqr);
        end
    endtask

    task body();
        init();

        fork
            run_reset();
        join_none

        #(100ns);

        fork
            run_seq_rand();
        join

        fork
            run_seq_read();
        join
    endtask

endclass
