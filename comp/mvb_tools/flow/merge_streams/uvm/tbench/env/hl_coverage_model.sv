// hl_coverage_model.sv: High-level coverage model for the stream coverage
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class hl_coverage_model #(int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS) extends uvm_subscriber #(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mvb_merge_streams::hl_coverage_model #(MVB_ITEM_WIDTH, RX_STREAMS))

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup stream_covergroup(string name = "stream_covergroup") with function sample(int unsigned stream_number);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        stream_number : coverpoint stream_number
        {
            bins stream[] = { [0 : RX_STREAMS-1] };
        }
    endgroup

    function string convert_to_full_name(string name);
        return { get_full_name(), ".", name };
    endfunction

    function new(string name = "hl_coverage_model", uvm_component parent = null);
        super.new(name, parent);

        stream_covergroup = new(convert_to_full_name("stream_covergroup"));
    endfunction

    function void write(uvm_logic_vector::sequence_item #(MVB_ITEM_WIDTH) t);
        int unsigned stream_number = t.data[$clog2(RX_STREAMS)-1 -: $clog2(RX_STREAMS)];

        stream_covergroup.sample(stream_number);
    endfunction

endclass
