// ll_coverage_model.sv: Low-level coverage model for the stream coverage
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class ll_coverage_model #(
    int unsigned MVB_ITEMS,
    int unsigned MVB_ITEM_WIDTH,
    int unsigned RX_STREAMS
) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_merge_streams::ll_coverage_model #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS))

    // ------ //
    // Inputs //
    // ------ //

    uvm_tlm_analysis_fifo #(uvm_mvb::sequence_item #(MVB_ITEMS, MVB_ITEM_WIDTH)) in[RX_STREAMS];

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup stream_covergroup(string name = "stream_covergroup") with function sample(int unsigned stream_count);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        stream_count : coverpoint stream_count
        {
            bins count[] = { [0 : RX_STREAMS] };
        }
    endgroup

    function string convert_to_full_name(string name);
        return { get_full_name(), ".", name };
    endfunction

    function new(string name = "ll_coverage_model", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < RX_STREAMS; i++) begin
            in[i] = new($sformatf("in_%0d", i), this);
        end

        stream_covergroup = new(convert_to_full_name("stream_covergroup"));
    endfunction

    task run_phase(uvm_phase phase);
        uvm_mvb::sequence_item #(MVB_ITEMS, MVB_ITEM_WIDTH) in_item;

        forever begin
            int unsigned simultaneously_active_stream_count = 0;

            for (int unsigned i = 0; i < RX_STREAMS; i++) begin
                in[i].get(in_item);

                if (in_item.src_rdy === 1'b1 && in_item.dst_rdy === 1'b1) begin
                    simultaneously_active_stream_count++;
                end
            end

            stream_covergroup.sample(simultaneously_active_stream_count);
        end
    endtask

endclass
