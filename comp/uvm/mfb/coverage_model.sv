// coverage_model.sv: Coverage model for the MFB
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class coverage_model #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH
) extends uvm_subscriber #(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH));
    `ndk_component_param_utils(
        uvm_mfb::coverage_model#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_mfb::coverage_model#(%0d,%0d,%0d,%0d,%0d)",REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    localparam int unsigned SOF_POS_WIDTH = ($clog2(REGION_SIZE) > 1)            ? $clog2(REGION_SIZE)            : 1;
    localparam int unsigned EOF_POS_WIDTH = ($clog2(REGION_SIZE*BLOCK_SIZE) > 1) ? $clog2(REGION_SIZE*BLOCK_SIZE) : 1;

    // ----------- //
    // Covergroups //
    // ----------- //

    // READY covergroup
    covergroup ready_covergroup with function sample(logic src_rdy, logic dst_rdy);
        option.name = {this.get_full_name(), ".ready"};
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

    covergroup packets with function sample (logic [REGIONS-1:0] sof, logic [REGIONS-1:0] eof, logic [REGIONS-1:0] sof_before);
        option.name = {this.get_full_name(), ".packets"};

        sof_num : coverpoint $countones(sof)
        {
            bins sofs[] = {[0 : REGIONS]};
        }

        eof_num : coverpoint $countones(eof)
        {
            bins eofs[] = {[0 : REGIONS]};
        }

        sof_before_eof : coverpoint $countones(sof & eof & sof_before)
        {
            bins sof_before[] = {[0 : REGIONS]};
        }

        sof_after_eof : coverpoint $countones(sof & eof & (~sof_before))
        {
            bins sof_after[] = {[0 : REGIONS]};
        }
    endgroup

    // SOF covergroup
    covergroup region with function sample(int unsigned region_num, logic sof, logic eof, int unsigned sof_pos, int unsigned eof_pos);
        option.name = {this.get_full_name(), ".region"};

        cov_sof_after_eof : coverpoint sof & eof & (sof_pos*BLOCK_SIZE > eof_pos) {
            bins sof_before = {1};
            bins sof_after  = {0};
        }

        cov_sof_position : coverpoint sof_pos iff sof === 1 {
            bins position [] = {[0:REGION_SIZE]};
        }

        cov_eof_position : coverpoint eof_pos iff eof === 1 {
            bins position [] = {[0:REGION_SIZE*BLOCK_SIZE]};
        }

        cov_region_num : coverpoint region_num {
            bins region [] = {[0:REGION_SIZE-1]};
        }



        // SOF x SOF_POS
        cov_reg_sof : cross cov_region_num, cov_sof_after_eof iff sof === 1;
    endgroup


    function new(string name = "coverage_model", uvm_component parent = null);
        super.new(name, parent);

        ready_covergroup  = new();
        packets           = new();
        region            = new();
    endfunction

    function void write(sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) t);
        logic [REGIONS-1:0] sof_before;

        ready_covergroup.sample(t.src_rdy, t.dst_rdy);


        if (t.src_rdy === 1'b1 && t.dst_rdy === 1'b1) begin
             for (int unsigned it = 0; it < REGIONS; it++) begin
                 // Sof is after active eof
                 if (t.sof[it] == 1 && t.eof[it] == 1 && t.sof_pos[it]*BLOCK_SIZE > t.eof_pos[it]) begin
                    sof_before[it] = 0;
                 end else begin
                    sof_before[it] = 1;
                 end
             end

            packets.sample(t.sof, t.eof, sof_before);

            for (int unsigned it = 0; it < REGIONS; it++) begin
                region.sample(it, t.sof[it], t.eof[it], t.sof_pos[it], t.eof_pos[it]);
            end
        end
    endfunction

endclass
