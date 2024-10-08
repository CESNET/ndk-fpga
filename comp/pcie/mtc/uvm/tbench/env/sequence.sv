//-- sequence.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_mi::sequence_master#(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0);
    `uvm_object_param_utils(uvm_mtc::mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH))

    uvm_mtc::tr_planner #(MI_DATA_WIDTH, MI_ADDR_WIDTH) tr_plan;

    function new(string name = "mi_cc_sequence");
        super.new(name);
    endfunction

    task body;
        req = uvm_mi::sequence_item_response #(MI_DATA_WIDTH)::type_id::create("req");

        forever begin
            uvm_logic_vector::sequence_item #(MI_DATA_WIDTH) hl_tr;

            if (tr_plan.mi_array.size() == 0) begin

                start_item(req);
                if(req.randomize() with {drdy == 0; drd == 0;} == 0) begin
                    `uvm_fatal(p_sequencer.get_full_name(), "mi_cc_sequence cannot randomize");
                end
                finish_item(req);

            end else begin
                hl_tr = tr_plan.mi_array.pop_front();
                start_item(req);
                if(req.randomize() with {drdy == 1;} == 0) begin
                    `uvm_fatal(p_sequencer.get_full_name(), "mi_cc_sequence cannot randomize");
                end
                finish_item(req);

            end

            get_response(rsp);
            save_request();
        end

    endtask
endclass
