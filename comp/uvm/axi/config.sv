//-- config.sv: Configuration object for AXI env
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef AXI_CONFIG_SV
`define AXI_CONFIG_SV

class config_sequence extends uvm_object;
    // configuration of probability of rdy signal in percentige
    int unsigned rdy_probability_min = 0;   // inside [0:100]
    int unsigned rdy_probability_max = 100; // inside [0:100]

    function void probability_set(int unsigned min, int unsigned max);
        rdy_probability_min = min;
        rdy_probability_max = max;
    endfunction
endclass


class config_item extends uvm_object;

    // ------------------------------------------------------------------------
    // Configuration variables
    uvm_active_passive_enum active;
    string interface_name;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name = "");
        super.new(name);
    endfunction

endclass

`endif
