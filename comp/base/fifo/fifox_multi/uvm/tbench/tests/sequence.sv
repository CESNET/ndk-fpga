// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequence #(DATA_WIDTH, READ_PORTS, MIN_TRANSACTION_COUNT, MAX_TRANSACTION_COUNT) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(DATA_WIDTH, READ_PORTS, MIN_TRANSACTION_COUNT, MAX_TRANSACTION_COUNT))
    `uvm_declare_p_sequencer(uvm_fifox_multi::virt_sequencer #(DATA_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start m_reset;

    uvm_logic_vector::sequence_simple  #(DATA_WIDTH) m_mvb_rx_seq;
    uvm_logic_vector::sequence_endless #(1)          m_mvb_rd_seq;

    uvm_phase phase;

    virtual function void init(uvm_phase phase);

        m_mvb_rx_seq = uvm_logic_vector::sequence_simple #(DATA_WIDTH)::type_id::create("m_mvb_rx_seq");
        m_mvb_rx_seq.transaction_count_min = MIN_TRANSACTION_COUNT;
        m_mvb_rx_seq.transaction_count_max = MAX_TRANSACTION_COUNT;

        m_mvb_rd_seq = uvm_logic_vector::sequence_endless #(1)::type_id::create("m_mvb_rd_seq");

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        this.phase = phase;

    endfunction

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);

    endtask

    virtual task run_mvb_rd_seq();

        forever begin
            m_mvb_rd_seq.randomize();
            m_mvb_rd_seq.start(p_sequencer.m_mvb_rd_sqr);
        end

    endtask

    virtual task run_mvb_rx_seq();

        m_mvb_rx_seq.randomize();
        m_mvb_rx_seq.start(p_sequencer.m_mvb_rx_sqr);

    endtask

    task body();

        fork
            run_reset();
        join_none

        #(100ns);

        fork
            // Run TX Sequencer
            run_mvb_rd_seq();
        join_none

        // Run RX Sequencer
        run_mvb_rx_seq();

    endtask

endclass
