//-- sequence.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class logic_vector_sequence#(META_WIDTH) extends uvm_sequence #(uvm_logic_vector::sequence_item#(META_WIDTH));
    `uvm_object_param_utils(uvm_pcie_adapter::logic_vector_sequence#(META_WIDTH))

    mailbox#(uvm_logic_vector::sequence_item#(META_WIDTH)) tr_export;

    function new(string name = "logic_vector_sequence");
        super.new(name);
    endfunction

    task body;
        forever begin
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass


class logic_vector_array_sequence#(ITEM_WIDTH) extends uvm_sequence #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_object_param_utils(uvm_pcie_adapter::logic_vector_array_sequence#(ITEM_WIDTH))

    mailbox#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) tr_export;

    function new(string name = "logic_vector_array_sequence");
        super.new(name);
    endfunction

    task body;
        forever begin
            tr_export.get(req);
            start_item(req);
            finish_item(req);
        end
    endtask
endclass


class crdt_sequence#(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W, PCIE_MPS_DW) extends uvm_sequence #(uvm_crdt::sequence_item);
    `uvm_object_param_utils(uvm_pcie_adapter::crdt_sequence#(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W, PCIE_MPS_DW))

    uvm_pcie_adapter::tr_planner #(CC_MFB_REGIONS, CC_MFB_REGION_SIZE, CC_MFB_BLOCK_SIZE, CC_MFB_ITEM_WIDTH, AVST_UP_META_W) tr_plan;
    uvm_logic_vector::sequence_item #(AVST_UP_META_W) meta;

    function new(string name = "logic_vector_array_sequence");
        super.new(name);
    endfunction

    task body;
        localparam SEED_MIN = (PCIE_MPS_DW/4)/15 + 1;
        localparam SEED_MAX = (PCIE_MPS_DW/4);
        logic [11-1 : 0] pcie_len;
        logic [8-1 : 0] pcie_type;
        logic [4-1 : 0] credits = '0;
        int unsigned cnt = 0;
        int unsigned credit_cnt = 0;
        logic hdr_valid = 1'b0;
        logic init = 1'b0;

        req = uvm_crdt::sequence_item::type_id::create("req");
        void'(std::randomize(cnt) with {cnt inside {[SEED_MIN : SEED_MAX]}; });

        forever begin
            if (tr_plan.tr_array.size() != 0 && init == 1'b1) begin
                credit_cnt = 0;
                meta = tr_plan.tr_array.pop_front();

                if (meta.data[106-1 : 96] == 0)
                    pcie_len  = 1024;
                else
                    pcie_len  = meta.data[106-1 : 96];

                if (pcie_len % 4 != 0) begin
                    pcie_len += 4 - (pcie_len % 4);
                end

                pcie_type = meta.data[128-1 : 120];

                hdr_valid = 1'b1;

                while (pcie_len/4 != credit_cnt) begin
                    start_item(req);

                    req.init_done = 1'b1;
                    req.update    = '0;
                    req.cnt_ph    = '0;
                    req.cnt_nph   = '0;
                    req.cnt_cplh  = '0;
                    req.cnt_pd    = '0;
                    req.cnt_npd   = '0;
                    req.cnt_cpld  = '0;

                    if (((pcie_len/4) - credit_cnt) >= 15) begin
                        void'(std::randomize(credits) with {credits inside {[1 : 15]}; });
                    end else begin
                        credits = (pcie_len/4) - credit_cnt;
                    end

                    credit_cnt += credits;

                    if (credit_cnt > pcie_len/4) begin
                        $write("Credit cnt %d\n", credit_cnt);
                        $write("pcie_len/4 %d\n", pcie_len/4);
                        `uvm_fatal(this.get_full_name(), "credit_cnt is bigger than pcie_len/4");
                    end

                    case (pcie_type)
                        8'b00000000 :
                        begin
                            if (hdr_valid == 1'b1) begin
                                req.update[1] = 1'b1;
                                req.cnt_nph   = 1'b1;
                                hdr_valid     = 1'b0;
                            end
                        end
                        8'b00100000 :
                        begin
                            if (hdr_valid == 1'b1) begin
                                req.update[1] = 1'b1;
                                req.cnt_nph   = 1'b1;
                                hdr_valid     = 1'b0;
                            end
                        end
                        8'b01001010 :
                        begin
                            req.update[5] = 1'b1;
                            if (hdr_valid == 1'b1) begin
                                req.update[2] = 1'b1;
                                req.cnt_cplh  = 1'b1;
                                hdr_valid     = 1'b0;
                            end
                            req.cnt_cpld = credits;
                        end
                        8'b01000000 :
                        begin
                            req.update[3] = 1'b1;
                            if (hdr_valid == 1'b1) begin
                                req.update[0] = 1'b1;
                                req.cnt_ph    = 1'b1;
                                hdr_valid     = 1'b0;
                            end
                            req.cnt_pd = credits;
                        end
                        8'b01100000 :
                        begin
                            req.update[3] = 1'b1;
                            if (hdr_valid == 1'b1) begin
                                req.update[0] = 1'b1;
                                req.cnt_ph    = 1'b1;
                                hdr_valid     = 1'b0;
                            end
                            req.cnt_pd = credits;
                        end
                    endcase

                    finish_item(req);
                end

            end else begin
                // Init phase
                start_item(req);
                req.init_done = 1'b1;
                req.update = '0;
                req.cnt_cpld = '0;
                req.cnt_cplh = '0;
                req.cnt_pd = '0;
                req.cnt_npd = '0;
                req.cnt_ph = '0;
                req.cnt_nph = '0;

                if (cnt > 0) begin
                    req.init_done = 1'b0;
                    req.update[0] = 1'b1;
                    req.cnt_ph = '1;
                    req.update[1] = 1'b1;
                    req.cnt_nph = '1;
                    req.update[2] = 1'b1;
                    req.cnt_cplh = '1;
                    req.update[3] = 1'b1;
                    req.cnt_pd = '1;
                    req.update[4] = 1'b1;
                    req.cnt_npd = '1;
                    req.update[5] = 1'b1;
                    req.cnt_cpld = '1;
                    cnt--;
                end else begin
                    req.init_done = 1'b1;
                    req.update = '0;
                    req.cnt_cpld = '0;
                    req.cnt_cplh = '0;
                    req.cnt_pd = '0;
                    req.cnt_npd = '0;
                    req.cnt_ph = '0;
                    req.cnt_nph = '0;
                    init = 1'b1;
                end
                finish_item(req);
            end
        end
    endtask
endclass