// Copyright (C) 2024 Intel Corporation
// SPDX-License-Identifier: MIT

//
// Generate a duplication tree for a register with large fanout. Most often,
// this is used to build a multi-cycle fanout of a reset.
//

module fim_dup_tree
  #(
    parameter MAX_FANOUT = 50,
    parameter TREE_DEPTH = 6,

    parameter DATA_WIDTH = 1,
    parameter bit [DATA_WIDTH-1:0] INIT_VALUE = 0
   )
   (
    input  logic clk,

    input  logic [DATA_WIDTH-1:0] din,
    output logic [DATA_WIDTH-1:0] dout
    );

    localparam MAX_FANOUT_STR = {"-name MAX_FANOUT ", $sformatf("%0d", MAX_FANOUT)};
    localparam DUP_HIERARCHY_STR = {"-name DUPLICATE_HIERARCHY_DEPTH ", $sformatf("%0d", TREE_DEPTH)};

    (* altera_attribute = {"-name DONT_MERGE_REGISTER ON; ", MAX_FANOUT_STR} *)
    reg [TREE_DEPTH-1:0] [DATA_WIDTH-1:0] dup_tree = {TREE_DEPTH{INIT_VALUE}};

    (* altera_attribute = {"-name DONT_MERGE_REGISTER ON; ", MAX_FANOUT_STR, "; ", DUP_HIERARCHY_STR} *)
    reg [DATA_WIDTH-1:0] dup_leaf = INIT_VALUE;

    always @(posedge clk) begin
        dup_tree <= { dup_tree[TREE_DEPTH-2:0], din };
        dup_leaf <= dup_tree[TREE_DEPTH-1];
    end

    assign dout = dup_leaf;

endmodule // fim_dup_tree
