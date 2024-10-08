// sequence.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequence #(DATA_WIDTH, MIN_TRANSACTION_COUNT, MAX_TRANSACTION_COUNT) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence #(DATA_WIDTH, MIN_TRANSACTION_COUNT, MAX_TRANSACTION_COUNT))
    `uvm_declare_p_sequencer(uvm_fifox::virt_sequencer #(DATA_WIDTH))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start m_reset;

    uvm_logic_vector::sequence_simple #(DATA_WIDTH) m_mvb_rx_seq;

    uvm_sequence #(uvm_mvb::sequence_item #(1, DATA_WIDTH)) m_mvb_tx_seq;
    uvm_mvb::sequence_lib_tx #(1, DATA_WIDTH) m_mvb_tx_seq_lib;

    uvm_phase phase;

    virtual function void init(uvm_phase phase);

        m_mvb_rx_seq = uvm_logic_vector::sequence_simple #(DATA_WIDTH)::type_id::create("m_mvb_rx_seq");
        m_mvb_rx_seq.transaction_count_min = MIN_TRANSACTION_COUNT;
        m_mvb_rx_seq.transaction_count_max = MAX_TRANSACTION_COUNT;

        m_mvb_tx_seq_lib = uvm_mvb::sequence_lib_tx #(1, DATA_WIDTH)::type_id::create("m_mvb_tx_seq_lib");
        m_mvb_tx_seq_lib.init_sequence();
        m_mvb_tx_seq_lib.min_random_count = 100;
        m_mvb_tx_seq_lib.max_random_count = 200;
        m_mvb_tx_seq = m_mvb_tx_seq_lib;

        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        this.phase = phase;

    endfunction

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);

    endtask

    virtual task run_mvb_tx_seq();

        forever begin
            m_mvb_tx_seq.randomize();
            m_mvb_tx_seq.start(p_sequencer.m_mvb_tx_sqr);
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
            run_mvb_tx_seq();
        join_none

        // Run RX Sequencer
        run_mvb_rx_seq();

    endtask

endclass
