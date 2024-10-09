// balance_splitter.sv: Splits a balance item into single credit counts
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class balance_splitter extends uvm_subscriber #(balance_item);
    `uvm_component_utils(uvm_pcie_intel_r_tile::balance_splitter)

    // Analysis ports
    uvm_analysis_port #(int unsigned) analysis_port[6];

    // Constructor
    function new(string name = "balance_splitter", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < 6; i++) begin
            analysis_port[i] = new($sformatf("analysis_port_%0d", i), this);
        end
    endfunction

    function void write(balance_item t);
        // HP
        analysis_port[0].write(t.header.p);
        // HNP
        analysis_port[1].write(t.header.np);
        // HCPL
        analysis_port[2].write(t.header.cpl);
        // DP
        analysis_port[3].write(t.data.p);
        // HNP
        analysis_port[4].write(t.data.np);
        // HCPL
        analysis_port[5].write(t.data.cpl);
    endfunction

endclass
