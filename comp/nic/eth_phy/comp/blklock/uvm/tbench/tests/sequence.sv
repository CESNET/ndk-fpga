/*
 * file       : sequence.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description:
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

//  All headers are valid and have SRC_RDY = '1'
class simple_sequence extends uvm_sequence #(uvm_mvb::sequence_item #(1, 2));
    `uvm_object_utils(test::simple_sequence);

    //  Group: Variables
    int max_trans =  1000;
    int min_trans =   100;
    rand int trans_count;

    //  Group: Constraints
    constraint tr_cnt_cons {trans_count inside {[min_trans:max_trans]};}

    function new(string name = "simple_sequence");
        super.new(name);
    endfunction

    task body;
        repeat (trans_count) begin
            `uvm_do_with(req, {req.vld[0] == 2'b1; req.dst_rdy == 2'b1; req.src_rdy == 2'b1; req.data[0] inside {[2'b01 : 2'b10]};});
        end
    endtask

endclass: simple_sequence

// All headers are invalid and have SRC_RDY = '1'
class simple_invalid_sequence extends uvm_sequence #(uvm_mvb::sequence_item #(1, 2));
    `uvm_object_utils(test::simple_invalid_sequence);

    //  Group: Variables
    int max_trans =  1000;
    int min_trans =   100;
    rand int trans_count;

    //  Group: Constraints
    constraint tr_cnt_cons {trans_count inside {[min_trans:max_trans]};}

    function new(string name = "simple_invalid_sequence");
        super.new(name);
    endfunction

    task body;
        repeat (trans_count) begin
            `uvm_do_with(req, {req.vld[0] == 2'b1; req.dst_rdy == 2'b1; req.src_rdy == 2'b1; req.data[0] inside {2'b00, 2'b11};});
        end
    endtask

endclass: simple_invalid_sequence

// SRC_RDY = '1', valid and invalid header count is distributed by parameters
class distributed_burst_sequence #(VALID_CNT, INVALID_CNT) extends uvm_sequence #(uvm_mvb::sequence_item #(1, 2));
    `uvm_object_param_utils(test::distributed_burst_sequence#(VALID_CNT, INVALID_CNT))

    //  Group: Variables
    int max_trans = 1000;
    int min_trans = 100;
    rand int trans_count;

    //  Group: Constraints
    constraint trans_count_constr {
        trans_count inside {[min_trans : max_trans]};
    }

    function new(string name = "distributed_burst_sequence");
        super.new(name);
    endfunction: new

    task body;
        repeat (trans_count) begin
            `uvm_do_with(req, {
                req.data[0] dist {[2'b01 : 2'b10] :/ VALID_CNT, 2'b00 :/ INVALID_CNT/2, 2'b11 :/ INVALID_CNT/2};
                req.vld[0] == 2'b1;
                req.dst_rdy == 2'b1;
                req.src_rdy == 2'b1; });
        end
    endtask
endclass: distributed_burst_sequence

// SRC_RDY is random, valid and invalid header count is distributed by parameters
class distributed_sequence #(VALID_CNT, INVALID_CNT) extends uvm_sequence #(uvm_mvb::sequence_item #(1, 2));
    `uvm_object_param_utils(test::distributed_sequence#(VALID_CNT, INVALID_CNT))

    //  Group: Variables
    int max_trans = 1000;
    int min_trans = 100;
    rand int trans_count;

    //  Group: Constraints
    constraint trans_count_constr {
        trans_count inside {[min_trans : max_trans]};
    }

    function new(string name = "distributed_sequence");
        super.new(name);
    endfunction: new

    task body;
        repeat (trans_count) begin
            `uvm_do_with(req, {
                req.data[0] dist {[2'b01 : 2'b10] :/ VALID_CNT, 2'b00 :/ INVALID_CNT/2, 2'b11 :/ INVALID_CNT/2};
                req.vld[0] == 2'b1;
                req.dst_rdy == 2'b1; });
        end
    endtask
endclass: distributed_sequence
