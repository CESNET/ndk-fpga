// coverage_model.sv: Coverage model for the MFB
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class coverage_model #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_subscriber #(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
    `uvm_component_param_utils(uvm_mfb::coverage_model #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    localparam int unsigned SOF_POS_WIDTH = ($clog2(REGION_SIZE) > 1)            ? $clog2(REGION_SIZE)            : 1;
    localparam int unsigned EOF_POS_WIDTH = ($clog2(REGION_SIZE*BLOCK_SIZE) > 1) ? $clog2(REGION_SIZE*BLOCK_SIZE) : 1;

    // ----------- //
    // Covergroups //
    // ----------- //

    // READY covergroup
    covergroup ready_covergroup(string name = "ready_covergroup") with function sample(logic src_rdy, logic dst_rdy);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        // Sequence of SRC_RDY
        src_rdy_sequence : coverpoint src_rdy
        {
            bins short  = (0 => 1 => 0);
            bins normal = (0 => 1[*2 :16] => 0);
            bins long   = (0 => 1[*17:32] => 0);
            bins huge   = default;
        }

        // Sequence of DST_RDY
        dst_rdy_sequence : coverpoint dst_rdy
        {
            bins short  = (0 => 1 => 0);
            bins normal = (0 => 1[*2 :16] => 0);
            bins long   = (0 => 1[*17:32] => 0);
            bins huge   = default;
        }

        // Sequence of reads
        read_sequence : coverpoint src_rdy & dst_rdy
        {
            bins short  = (0 => 1 => 0);
            bins normal = (0 => 1[*2 :16] => 0);
            bins long   = (0 => 1[*17:32] => 0);
            bins huge   = default;
        }
    endgroup

    // SOF covergroup
    covergroup sof_covergroup(string name = "sof_covergroup") with function sample(int unsigned sof_region, logic [SOF_POS_WIDTH-1 : 0] sof_pos);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        // SOF
        sof_region : coverpoint sof_region
        {
            bins sof_region[] = { [0 : REGIONS-1] };
        }

        // SOF_POS
        sof_pos : coverpoint sof_pos
        {
            bins sof_pos[] = { [0 : (2**SOF_POS_WIDTH)-1] };
        }

        // SOF x SOF_POS
        sof_region_x_sof_pos : cross sof_region, sof_pos;
    endgroup

    // EOF covergroup
    covergroup eof_covergroup(string name = "eof_covergroup") with function sample(int unsigned eof_region, logic [EOF_POS_WIDTH-1 : 0] eof_pos);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        // EOF
        eof_region : coverpoint eof_region
        {
            bins eof[] = { [0 : REGIONS-1] };
        }

        // EOF_POS
        eof_pos : coverpoint eof_pos
        {
            bins eof_pos[] = { [0 : (2**EOF_POS_WIDTH)-1] };
        }

        // EOF x EOF_POS
        eof_region_x_eof_pos : cross eof_region, eof_pos;
    endgroup

    // Count of SOFs and EOFs within a data word
    covergroup count_sof_eof_covergroup(string name = "count_sof_eof_covergroup") with function sample(int unsigned sof_count, int unsigned eof_count);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        // SOF count
        sof_count : coverpoint sof_count
        {
            bins count[] = { [0 : REGIONS] };
        }

        // EOF count
        eof_count : coverpoint eof_count
        {
            bins count[] = { [0 : REGIONS] };
        }
    endgroup

    function string convert_to_full_name(string name);
        return { get_full_name(), ".", name };
    endfunction

    function new(string name = "coverage_model", uvm_component parent = null);
        super.new(name, parent);

        ready_covergroup         = new(convert_to_full_name("ready_covergroup"));
        sof_covergroup           = new(convert_to_full_name("sof_covergroup"));
        eof_covergroup           = new(convert_to_full_name("eof_covergroup"));
        count_sof_eof_covergroup = new(convert_to_full_name("count_sof_eof_covergroup"));
    endfunction

    function void write(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) t);
        ready_covergroup.sample(t.src_rdy, t.dst_rdy);

        if (t.src_rdy === 1'b1 && t.dst_rdy === 1'b1) begin
            count_sof_eof_covergroup.sample($countones(t.sof), $countones(t.eof));

            for (int unsigned i = 0; i < REGIONS; i++) begin
                if (t.sof[i] === 1'b1) begin
                    sof_covergroup.sample(i, t.sof_pos[i]);
                end
                if (t.eof[i] === 1'b1) begin
                    eof_covergroup.sample(i, t.eof_pos[i]);
                end
            end
        end
    endfunction

endclass
