// valuer.sv: Converts logic vector sequence items into balance items
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class valuer #(META_WIDTH) extends uvm_subscriber #(uvm_logic_vector::sequence_item #(META_WIDTH));
    `uvm_component_param_utils(uvm_pcie_intel_r_tile::valuer #(META_WIDTH))

    localparam int unsigned HDR_WIDTH    = 128;
    localparam int unsigned PREFIX_WIDTH = 32;

    // Output
    uvm_analysis_port #(balance_item) analysis_port;

    // Constructor
    function new(string name = "transaction_checker", uvm_component parent = null);
        super.new(name, parent);

        analysis_port = new("analysis_port", this);
    endfunction

    function void write(uvm_logic_vector::sequence_item #(META_WIDTH) t);
        balance_item cost = get_transaction_cost(t);
        analysis_port.write(cost);
    endfunction

    function balance_item get_transaction_cost(uvm_logic_vector::sequence_item #(META_WIDTH) item);
        balance_item cost;

        logic [HDR_WIDTH   -1 : 0] hdr;
        logic [PREFIX_WIDTH-1 : 0] prefix;
        logic [1           -1 : 0] error;
        logic [3           -1 : 0] fmt;
        logic [5           -1 : 0] pcie_type;
        logic [1           -1 : 0] r0;
        logic [3           -1 : 0] tc;
        logic [1           -1 : 0] r1;
        logic [1           -1 : 0] attr0;
        logic [1           -1 : 0] r2;
        logic [1           -1 : 0] th;
        logic [1           -1 : 0] td;
        logic [1           -1 : 0] ep;
        logic [2           -1 : 0] attr1;
        logic [2           -1 : 0] at;
        logic [10          -1 : 0] length;

        { error, prefix, hdr } = item.data;
        { fmt, pcie_type, r0, tc, r1, attr0, r2, th, td, ep, attr1, at, length } = hdr[32*4-1 -: 32];

        cost = balance_item::type_id::create("cost");

        // Completion with Data
        if ({ fmt, pcie_type } === 8'b01001010) begin
            cost.header.cpl = 1;
            cost.data  .cpl = get_data_cost(length);
        end
        // Request with Data
        else if (fmt[2 : 1] === 2'b01) begin
            cost.header.p = 1;
            cost.data  .p = get_data_cost(length);
        end
        // Request without Data
        else begin
            cost.header.np = 1;
        end

        return cost;
    endfunction

    function int unsigned get_data_cost(logic [10-1 : 0] length);
        return ((((length === 10'b0) ? 1024 : length) - 1) / 4) + 1; // TLP length => credit value
    endfunction

endclass
