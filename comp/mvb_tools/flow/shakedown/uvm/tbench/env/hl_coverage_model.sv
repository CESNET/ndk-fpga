// hl_coverage_model.sv: High-level coverage model for the port activity coverage
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class hl_coverage_model #(int unsigned TX_ITEMS) extends uvm_subscriber #(read_command_item #(TX_ITEMS));
    `uvm_component_param_utils(uvm_mvb_shakedown::hl_coverage_model #(TX_ITEMS))

    // ----------- //
    // Covergroups //
    // ----------- //

    covergroup port_covergroup(string name = "port_covergroup") with function sample(int unsigned port_number);
        option.name = name;
        option.per_instance = 1;

        // =========== //
        // Coverpoints //
        // =========== //

        port_number : coverpoint port_number
        {
            bins port[] = { [0 : TX_ITEMS-1] };
        }
    endgroup

    function string convert_to_full_name(string name);
        return { get_full_name(), ".", name };
    endfunction

    function new(string name = "hl_coverage_model", uvm_component parent = null);
        super.new(name, parent);

        port_covergroup = new(convert_to_full_name("port_covergroup"));
    endfunction

    function void write(read_command_item #(TX_ITEMS) t);
        for (int unsigned i = 0; i < TX_ITEMS; i++) begin
            if (t.read[i] === 1'b1) begin
                port_covergroup.sample(i);
            end
        end
    endfunction

endclass
