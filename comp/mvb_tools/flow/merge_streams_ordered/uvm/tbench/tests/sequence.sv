// sequence.sv: Virtual sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class virt_sequence#(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_sequence#(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))
    `uvm_declare_p_sequencer(uvm_mvb_merge_streams_ordered::virt_sequencer#(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    function new (string name = "virt_sequence");
        super.new(name);
    endfunction

    uvm_reset::sequence_start                              m_reset;
    uvm_logic_vector::sequence_simple#(MVB_ITEM_WIDTH)     m_rx_mvb_seq [RX_STREAMS - 1 : 0];
    uvm_logic_vector::sequence_simple#($clog2(RX_STREAMS)) m_rx_sel_mvb_seq;


    virtual function void init();
        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        for (int port = 0; port < RX_STREAMS; port++) begin
            m_rx_mvb_seq[port] = uvm_logic_vector::sequence_simple#(MVB_ITEM_WIDTH)::type_id::create($sformatf("m_rx_mvb_seq_%0d", port));
            m_rx_mvb_seq[port].transaction_count_min = MIN_TRANSACTION_COUNT;
            m_rx_mvb_seq[port].transaction_count_max = MAX_TRANSACTION_COUNT;
        end

        m_rx_sel_mvb_seq = uvm_logic_vector::sequence_simple#($clog2(RX_STREAMS))::type_id::create("m_rx_sel_mvb_seq");
        m_rx_sel_mvb_seq.transaction_count_min = MIN_TRANSACTION_COUNT;
        m_rx_sel_mvb_seq.transaction_count_max = MAX_TRANSACTION_COUNT;
    endfunction

    virtual task run_reset();

        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset_sqcr);

    endtask // run_reset

    virtual task run_mvb_select();
        repeat (RUNS) begin
            m_rx_sel_mvb_seq.randomize();
            m_rx_sel_mvb_seq.start(p_sequencer.m_rx_sel_mvb_sqcr);
        end
    endtask;

    virtual task run_mvb_per_port(int unsigned port);
        forever begin
            m_rx_mvb_seq[port].randomize();
            m_rx_mvb_seq[port].start(p_sequencer.m_rx_mvb_sqcr[port]);
        end
    endtask

    virtual task run_mvb();
        for (int unsigned port = 0; port < RX_STREAMS; port++) begin
            fork
                automatic int unsigned x = port;
                run_mvb_per_port(x);
            join_none;
        end
    endtask

    task body();

        init();

        fork
            run_reset();
        join_none

        #(200ns)

        run_mvb();
        run_mvb_select();
    endtask // body
endclass
