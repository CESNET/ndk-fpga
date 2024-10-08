// coverage.sv: Coverage for the LBUS interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class coverage extends uvm_subscriber #(sequence_item);
    `uvm_component_utils(uvm_lbus::coverage)

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup ready_covergroup with function sample(sequence_item item);
        ready : coverpoint item.rdy {
            bins short   = (0 => 1 => 0);
            bins longer  = (0 => 1[*2:16]  => 0);
            bins long    = (0 => 1[*17:32] => 0);
            bins longest = default;
        }
    endgroup

    // Constructor
    function new(string name = "coverage", uvm_component parent = null);
        super.new(name, parent);

        ready_covergroup = new();
    endfunction

    function void write(sequence_item t);
        ready_covergroup.sample(t);
    endfunction

    function void report_phase(uvm_phase phase);
        string report_message = $sformatf("\n\tRDY coverage: %0f%%\n", ready_covergroup.get_inst_coverage());

        super.report_phase(phase);

        `uvm_info(this.get_full_name(), report_message, UVM_LOW);
    endfunction

endclass
