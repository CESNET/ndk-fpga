// sequencer.sv: Sequencer for AVST credit control interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequencer #(int unsigned UPDATE_CNT_WIDTH) extends uvm_avst_crdt::sequencer #(UPDATE_CNT_WIDTH);
    `uvm_component_param_utils(uvm_pcie_intel_r_tile::sequencer #(UPDATE_CNT_WIDTH))

    // Reset
    uvm_reset::sync_terminate reset_sync;

    // Input export
    uvm_analysis_imp #(int unsigned, sequencer #(UPDATE_CNT_WIDTH)) analysis_export;

    // Total balance to return
    int unsigned total;

    // Constructor
    function new(string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();

        analysis_export = new("analysis_export", this);

        total = 0;
    endfunction

    function void write(int unsigned t);
        if (reset_sync.has_been_reset()) begin
            total = 0;
            return;
        end

        total += t;
    endfunction

endclass
