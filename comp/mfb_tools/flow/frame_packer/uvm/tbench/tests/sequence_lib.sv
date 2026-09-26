// sequence_lib.sv: Additional sequences of the verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


// Small packets directly followed by packets close to the maximal size
// Several SOFs of one channel fall into one MFB word together with a big packet (SuperPacket size limit)
class sequence_small_big #(
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_base #(uvm_logic_vector_array::config_sequence,
                                      uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));
    `uvm_object_param_utils(test::sequence_small_big#(ITEM_WIDTH))

    int unsigned transaction_count_min = 10;
    int unsigned transaction_count_max = 100;
    rand int unsigned transaction_count;

    protected int unsigned size_min;
    protected int unsigned size_max;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    function new(string name = "sequence_small_big");
        super.new(name);
    endfunction

    task body;
        const int unsigned SIZE_RANGE = 64;

        for (int unsigned it = 0; it < transaction_count; it++) begin
            if (it % 2 == 0) begin
                size_min = cfg.array_size_min;
                size_max = (cfg.array_size_min + SIZE_RANGE < cfg.array_size_max) ?
                               cfg.array_size_min + SIZE_RANGE : cfg.array_size_max;
            end else begin
                size_min = (cfg.array_size_max > cfg.array_size_min + SIZE_RANGE) ?
                               cfg.array_size_max - SIZE_RANGE : cfg.array_size_min;
                size_max = cfg.array_size_max;
            end
            `uvm_do_with(req, {data.size inside {[local::size_min : local::size_max]};});
        end
    endtask
endclass


// TX MVB DST_RDY is held low for MVB_TX_STALL_CLKS clock cycles at the beginning of the test while TX MFB keeps
// running - all MVB items of the SuperPackets sent in the meantime have to be stored in the DUT
class mvb_tx_lib_stall #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
) extends uvm_mvb::sequence_lib_tx #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(test::mvb_tx_lib_stall#(ITEMS, ITEM_WIDTH))

    // The environment restarts the TX library in a loop, the stall is applied only once
    static bit stall_done = 1'b0;

    function new(string name = "mvb_tx_lib_stall");
        super.new(name);
    endfunction

    task body();
        if (!stall_done) begin
            uvm_mvb::sequence_stop_tx #(ITEMS, ITEM_WIDTH) stop_seq;

            stall_done = 1'b1;
            stop_seq = uvm_mvb::sequence_stop_tx #(ITEMS, ITEM_WIDTH)::type_id::create("stop_seq");
            stop_seq.min_transaction_count = MVB_TX_STALL_CLKS;
            stop_seq.max_transaction_count = MVB_TX_STALL_CLKS;
            stop_seq.config_set(cfg);
            assert(stop_seq.randomize());
            stop_seq.start(m_sequencer, this);
        end
        super.body();
    endtask
endclass
