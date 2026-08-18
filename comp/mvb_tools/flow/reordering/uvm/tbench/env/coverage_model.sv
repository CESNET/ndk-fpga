// coverage_model.sv: Coverage model for the frame-extending functionality
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

class coverage_model #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH
    ) extends uvm_subscriber#(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH + $clog2(ITEMS)));
    `uvm_component_param_utils(uvm_mvb_reordering::coverage_model #(ITEMS, ITEM_WIDTH))

    static function automatic longint unsigned factorial(int unsigned n);
        return (n <= 1) ? 1 : n * factorial(n - 1);
    endfunction

    // KEY_WIDTH must be at least 1 to avoid invalid ranges when ITEMS=1
    localparam int unsigned KEY_WIDTH = ($clog2(ITEMS) == 0) ? 1 : $clog2(ITEMS);

    // Factorial for permutation bin count
    localparam int unsigned PERMUTATION_BINS = factorial(ITEMS);

    // ------ //
    // Inputs //
    // ------ //

    uvm_tlm_analysis_fifo #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH + $clog2(ITEMS))) in;

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup reorder_covergroup(
        string name = "reorder_covergroup"
    ) with function sample (
        bit src_ready, bit dst_ready,
        logic [KEY_WIDTH-1:0] key_arr [ITEMS],
        logic [ITEMS-1:0] vld,
        input int unsigned permutation_idx
    );
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        // src ready
        src_ready : coverpoint { src_ready }
        {
            bins s_ready  = { 1'b1 };
            bins s_not_ready = { 1'b0 };
        }

        // dst ready
        dst_ready : coverpoint { dst_ready }
        {
            bins d_ready  = { 1'b1 };
            bins d_not_ready = { 1'b0 };
        }

        cross src_ready, dst_ready;

        // Key values (only for ITEMS > 1)
        key_values : coverpoint key_arr[0] {
            option.weight = (ITEMS == 1) ? 0 : 1;
            bins key_bins[] = {[0:ITEMS-1]};
        }

        // 2**ITEMS = 8  →  bins 0‑7
        vld_vals : coverpoint vld  {
            bins vld_bins[2**ITEMS] = {[0:2**ITEMS-1]};
        }

        // Cross: key values × vld (only for ITEMS > 1)
        key_vld_cross : cross key_values, vld {
            option.weight = (ITEMS == 1) ? 0 : 1;
        }

        // Permutation coverage: all possible positions of unique keys (only for ITEMS > 1)
        key_permutation : coverpoint permutation_idx {
            option.weight = (ITEMS == 1) ? 0 : 1;
            bins permutations[] = {[0:PERMUTATION_BINS-1]};
        }

    endgroup

    function new(string name = "coverage_model", uvm_component parent = null);
        super.new(name, parent);

        reorder_covergroup = new({ get_full_name(), ".", "reorder_covergroup" });
    endfunction

    function void write(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH + $clog2(ITEMS)) t);
        bit src_ready;
        bit dst_ready;
        logic [ITEMS-1:0] vld;
        logic [KEY_WIDTH-1:0] key;
        logic [KEY_WIDTH-1:0] key_arr [ITEMS];
        int unsigned permutation_idx;
        int unsigned factorial_val;
        int unsigned count_smaller;
        int unsigned i, j;

        src_ready = t.src_rdy;
        dst_ready = t.dst_rdy;
        vld = t.vld;

        // Extract ALL keys from ALL positions in one cycle
        for (i = 0; i < ITEMS; i++) begin
            key_arr[i] = t.data[i][ITEM_WIDTH + KEY_WIDTH-1 -: KEY_WIDTH];
        end

        // Compute permutation index maps each unique permutation to a number from 0 to ITEMS!-1
        permutation_idx = 0;
        for (i = 0; i < ITEMS; i++) begin
            factorial_val = 1;
            for (j = 1; j < ITEMS - i; j++) begin
                factorial_val *= j;
            end
            count_smaller = 0;
            for (j = i + 1; j < ITEMS; j++) begin
                if (key_arr[j] < key_arr[i]) begin
                    count_smaller++;
                end
            end
            permutation_idx += count_smaller * factorial_val;
        end

        // Sample once per cycle with permutation index
        reorder_covergroup.sample(src_ready, dst_ready, key_arr, vld, permutation_idx);
    endfunction

endclass
