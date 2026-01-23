// virtual_sequence_base.sv: Virtual base sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_base #(
    int unsigned MVB_ITEMS,
    int unsigned MVB_ITEM_WIDTH,
    int unsigned RX_STREAMS
) extends uvm_sequence;
    `uvm_object_param_utils(test::virtual_sequence_base #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))
    `uvm_declare_p_sequencer(uvm_mvb_merge_streams::virtual_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    uvm_reset::sequence_start                              m_reset;
    data_sequence            #(MVB_ITEM_WIDTH, RX_STREAMS) m_rx_mvb[RX_STREAMS];

    protected logic [RX_STREAMS-1:0] m_rx_mvb_active;
    function new(string name = "virtual_sequence_base");
        super.new(name);
    endfunction

    virtual function void init();
        // Create the reset sequence
        m_reset = uvm_reset::sequence_start::type_id::create("m_reset");

        // ---------------- //
        // RX MVB sequences //
        // ---------------- //

        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            // Create the RX MVB sequence
            m_rx_mvb[i] = data_sequence #(MVB_ITEM_WIDTH, RX_STREAMS)::type_id::create($sformatf("m_rx_mvb_%0d", i));
            // Configure the RX MVB sequence
            m_rx_mvb[i].stream_number = i;
            m_rx_mvb[i].transaction_count_min = 300;
            m_rx_mvb[i].transaction_count_max = 500;
        end
    endfunction

    task body();

        m_rx_mvb_active = '1;

        // Run the reset sequence
        fork
            begin
                assert(m_reset.randomize());
                m_reset.start(p_sequencer.m_reset);
            end
        join_none

        #(100ns);

        // Run the RX MVB sequences
        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            fork
                int unsigned i_local = i;
                begin
                    assert(m_rx_mvb[i_local].randomize());
                    m_rx_mvb[i_local].start(p_sequencer.m_rx_mvb[i_local]);
                    m_rx_mvb_active[i_local] = 0;
                end
            join_none
        end

        wait (m_rx_mvb_active == 0);
    endtask

endclass
