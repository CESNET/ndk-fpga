// sequence_mi.sv : sequence generating mi responses
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

// This low level sequence define bus functionality
class mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_mi::sequence_master#(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0);
    `uvm_object_param_utils(uvm_pcie_top::mi_cc_sequence #(MI_DATA_WIDTH, MI_ADDR_WIDTH))

    rand int unsigned transactions;
    int unsigned read_cnt;
    int unsigned write_cnt;
    protected int unsigned read_active;

    constraint tr_num_c {
        transactions inside {[200:1000]};
    }

    function new(string name = "mi_cc_sequence");
        super.new(name);
        read_cnt    = 0;
        write_cnt   = 0;
        read_active = 0;
    endfunction

    task body;
        int unsigned it = 0;
        req = uvm_mi::sequence_item_response #(MI_DATA_WIDTH)::type_id::create("req");

        while (read_active != 0 || it < transactions) begin
            //uvm_logic_vector::sequence_item #(1) hl_tr;
            start_item(req);
            assert(req.randomize() with {
                req.ardy dist { 1'b0 :/ 20, 1'b1 := 80};
                read_active == 0 -> req.drdy == 0;
                read_active != 0 -> req.drdy dist { 1'b0 :/ 10, 1'b1 := read_active};}) else begin
                `uvm_fatal(p_sequencer.get_full_name(), "mi_cc_sequence cannot randomize");
            end
            finish_item(req);
            if(req.drdy == 1'b1) begin
                read_active--;
            end


            get_response(rsp);
            if (req.ardy == 1'b1 && rsp.rd == 1'b1) begin 
                read_active++;
                read_cnt++;
            end
            if (req.ardy == 1'b1 && rsp.wr == 1'b1) begin 
                write_cnt++;
            end
            save_request();

            it++;
        end

    endtask
endclass
