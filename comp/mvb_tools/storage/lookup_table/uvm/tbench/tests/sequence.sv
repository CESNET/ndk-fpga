// sequence.sv: Virtual sequence
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequence#(ITEMS, LUT_WIDTH, REG_DEPTH, ADDR_WIDTH, SLICE_WIDTH, SW_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(ITEMS, LUT_WIDTH, REG_DEPTH, ADDR_WIDTH, SLICE_WIDTH, SW_WIDTH))
    `uvm_declare_p_sequencer(uvm_lookup_table::virt_sequencer#(ITEMS, LUT_WIDTH, REG_DEPTH, SLICE_WIDTH, SW_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                                                   m_reset;
    uvm_logic_vector::sequence_simple#(REG_DEPTH-SLICE_WIDTH)                   m_logic_vector_sq;
    uvm_lookup_table::reg_sequence#(REG_DEPTH, ADDR_WIDTH, LUT_DEPTH, SW_WIDTH) m_reg;
    uvm_mvb::sequence_lib_tx#(MVB_ITEMS, LUT_WIDTH)                             h_seq_tx;
    uvm_phase phase;

    virtual function void init(uvm_lookup_table::regmodel#(REG_DEPTH, SW_WIDTH) m_regmodel, uvm_phase phase);

        m_reset           = uvm_reset::sequence_start::type_id::create("m_reset");
        m_logic_vector_sq = uvm_logic_vector::sequence_simple#(REG_DEPTH-SLICE_WIDTH)::type_id::create("m_logic_vector_sq");
        m_reg             = uvm_lookup_table::reg_sequence#(REG_DEPTH, ADDR_WIDTH, LUT_DEPTH, SW_WIDTH)::type_id::create("m_reg");
        m_reg.m_regmodel  = m_regmodel;

        h_seq_tx = uvm_mvb::sequence_lib_tx #(MVB_ITEMS, LUT_WIDTH)::type_id::create("h_seq_tx");
        h_seq_tx.init_sequence();
        h_seq_tx.cfg.probability_set(60, 100);
        h_seq_tx.min_random_count = 200;
        h_seq_tx.max_random_count = 500;
        this.phase = phase;

    endfunction

    task run_seq_tx(uvm_phase phase);
        forever begin
            h_seq_tx.randomize();
            h_seq_tx.start(p_sequencer.m_tx_sqr);
        end
    endtask

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset_sqr);

    endtask

    task body();

        // init();

        fork
            run_reset();
        join_none

        #(200ns)

        fork
            run_seq_tx(phase);
        join_none

        #(200ns)

        fork
            m_reg.randomize();
            m_reg.start(null);
        join_none

        #(5000ns)

        for (int unsigned it = 0; it < REPEAT; it++) begin
            run_mfb();
        end

    endtask

    virtual task run_mfb();
        m_logic_vector_sq.randomize();
        m_logic_vector_sq.start(p_sequencer.m_logic_vector_scr);
    endtask

endclass
