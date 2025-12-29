// valuer.sv: Converts logic vector sequence items into balance items
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class valuer extends uvm_subscriber #(uvm_pcie::header);
    `uvm_component_param_utils(uvm_pcie_intel_r_tile::valuer)

    // Output
    uvm_analysis_port #(balance_item) analysis_port;

    // Constructor
    function new(string name = "transaction_checker", uvm_component parent = null);
        super.new(name, parent);

        analysis_port = new("analysis_port", this);
    endfunction

    function void write(uvm_pcie::header t);
        balance_item cost = get_transaction_cost(t);
        analysis_port.write(cost);
    endfunction

    function balance_item get_transaction_cost(uvm_pcie::header hdr);
        balance_item cost;

        cost = balance_item::type_id::create("cost");

        // Completion with Data
        if ({ hdr.fmt, hdr.pcie_type } === 8'b01001010) begin
            cost.header.cpl = 1;
            cost.data  .cpl = get_data_cost(hdr.length_get());
        end
        // Request with Data
        else if (hdr.fmt[2 : 1] === 2'b01) begin
            cost.header.p = 1;
            cost.data  .p = get_data_cost(hdr.length_get());
        end
        // Request without Data
        else begin
            cost.header.np = 1;
        end

        return cost;
    endfunction

    function int unsigned get_data_cost(int unsigned length);
        return ((length + 3) / 4); // TLP length => credit value
    endfunction
endclass
