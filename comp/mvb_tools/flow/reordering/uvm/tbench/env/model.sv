// model.sv: Model of implementation
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

class model #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    bit REORDERING_EN
) extends uvm_component;
    `uvm_component_param_utils(uvm_mvb_reordering::model #(ITEMS, ITEM_WIDTH, REORDERING_EN))

    // Model inputs
    uvm_tlm_analysis_fifo #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH + $clog2(ITEMS))) model_mvb_in;

    // Model outputs
    uvm_analysis_port #(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)) model_mvb_out;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        model_mvb_in  = new("model_mvb_in",  this);
        model_mvb_out = new("model_mvb_out", this);
    endfunction

    task run_phase(uvm_phase phase);

        uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH + $clog2(ITEMS)) tr_mvb_in;
        uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH) tr_mvb_out;

        forever begin
            logic [$clog2(ITEMS)-1:0] key;
            logic [ITEM_WIDTH-1:0]    data;
            // Gets the input transaction
            model_mvb_in.get(tr_mvb_in);

            // Sends the output transaction
            if (tr_mvb_in.src_rdy === 1 && tr_mvb_in.dst_rdy === 1) begin
                tr_mvb_out = uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("tr_mvb_out", this);
                tr_mvb_out.src_rdy = 1;
                tr_mvb_out.dst_rdy = 1;

                for (int unsigned item = 0; item < ITEMS; item++) begin
                    tr_mvb_out.data[item] = 'x;
                    tr_mvb_out.vld[item] = 0;
                end

                if (ITEMS > 1 && REORDERING_EN) begin
                    for (int unsigned item = 0; item < ITEMS; item++) begin
                        if (tr_mvb_in.vld[item]) begin
                            {key, data} = tr_mvb_in.data[item];
                            tr_mvb_out.data[key] = data;
                            tr_mvb_out.vld[key] = 1;
                        end
                    end
                end else begin // key size is 0
                    tr_mvb_out.vld  = tr_mvb_in.vld;

                    for (int unsigned item = 0; item < ITEMS; item++) begin
                        {key, data} = tr_mvb_in.data[item];
                        tr_mvb_out.data[item] = data;
                    end
                end

                model_mvb_out.write(tr_mvb_out);
            end

        end

    endtask

endclass
