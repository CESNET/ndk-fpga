// virtual_sequence_speed.sv: Virtual speed sequence
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class virtual_sequence_speed #(int unsigned MVB_ITEMS, int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends virtual_sequence_base #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS);
    `uvm_object_param_utils(test::virtual_sequence_speed #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))
    `uvm_declare_p_sequencer(uvm_mvb_merge_streams::virtual_sequencer #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    uvm_mvb::sequence_lib_tx_speed #(MVB_ITEMS, MVB_ITEM_WIDTH) m_tx_mvb;

    function new(string name = "virtual_sequence_speed");
        super.new(name);
    endfunction

    function void init();
        super.init();

        // --------------- //
        // TX MVB sequence //
        // --------------- //

        m_tx_mvb = uvm_mvb::sequence_lib_tx_speed #(MVB_ITEMS, MVB_ITEM_WIDTH)::type_id::create("m_tx_mvb");
        m_tx_mvb.init_sequence();
        m_tx_mvb.min_random_count = 150;
        m_tx_mvb.max_random_count = 200;
    endfunction

    task body();
        // Run the reset sequence
        fork
            begin
                assert(m_reset.randomize());
                m_reset.start(p_sequencer.m_reset);
            end
        join_none

        #(100ns);

        // Run the TX MVB sequence
        fork
            forever begin
                assert(m_tx_mvb.randomize());
                m_tx_mvb.start(p_sequencer.m_tx_mvb);
            end
        join_none

        // Run the RX MVB sequences
        fork
            begin
                for (int unsigned i = 0; i < RX_STREAMS; i++) begin
                    fork
                        int unsigned i_local = i;
                        begin
                            assert(m_rx_mvb[i_local].randomize());
                            m_rx_mvb[i_local].start(p_sequencer.m_rx_mvb[i_local]);
                        end
                    join_none
                end
                wait fork;
            end
        join
    endtask

endclass
