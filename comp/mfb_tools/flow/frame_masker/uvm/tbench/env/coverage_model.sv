// coverage_model.sv: Coverage model
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class coverage_model #(int unsigned MFB_REGIONS, int unsigned MFB_REGION_SIZE, int unsigned MFB_BLOCK_SIZE, int unsigned MFB_ITEM_WIDTH, int unsigned MFB_META_WIDTH) extends uvm_component;
    `uvm_component_param_utils(frame_masker::coverage_model #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    `uvm_analysis_imp_decl(_discard)
    `uvm_analysis_imp_decl(_frame)

    uvm_analysis_imp_discard #(
        bit,
        frame_masker::coverage_model #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)
    ) input_discard;

    uvm_analysis_imp_frame #(
        uvm_mfb::sequence_item #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH),
        frame_masker::coverage_model #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)
    ) input_frame;

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup discard_covergroup(string name = "discard_covergroup") with function sample(bit discarded);
        option.name = name;

        // =========== //
        // Coverpoints //
        // =========== //

        coverpoint discarded
        {
            bins discarded = { 1 };
            bins passed    = { 0 };
        }

    endgroup

    covergroup frame_count_covergroup(string name = "frame_count_covergroup") with function sample(int unsigned frame_count);
        option.name = name;

        // =========== //
        // Coverpoints //
        // =========== //

        coverpoint frame_count
        {
            bins frame_count[] = { [0 : MFB_REGIONS] };
        }
    endgroup

    function new(string name = "coverage_model", uvm_component parent = null);
        super.new(name, parent);

        input_discard = new("input_discard", this);
        input_frame   = new("input_frame", this);

        discard_covergroup     = new("discard_covergroup");
        frame_count_covergroup = new("frame_count_covergroup");
    endfunction

    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);

        // It doesn't make sense for MFB_REGIONS=1
        if (MFB_REGIONS == 1) begin
            discard_covergroup.option.weight      = 0;
            discard_covergroup.type_option.weight = 0;
        end
    endfunction

    function void write_discard(bit t);
        discard_covergroup.sample(t);
    endfunction

    function void write_frame(uvm_mfb::sequence_item #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) t);
        int unsigned frame_count;

        if (t.src_rdy !== 1'b1 || t.dst_rdy !== 1'b1) begin
            return;
        end

        frame_count = $countones(t.sof);
        frame_count_covergroup.sample(frame_count);
    endfunction

endclass
