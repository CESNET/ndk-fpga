// port_watchdog.sv: Watches a port and generates information if the port has been read
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

class port_watchdog #(int unsigned ITEM_WIDTH) extends uvm_subscriber #(uvm_logic_vector::sequence_item #(ITEM_WIDTH));
    `uvm_component_param_utils(uvm_mvb_shakedown::port_watchdog #(ITEM_WIDTH))

    // The number of the port it is watching
    int unsigned port_number;

    // Output
    uvm_analysis_port #(int unsigned) analysis_port;

    function new(string name = "port_watchdog", uvm_component parent = null);
        super.new(name, parent);

        analysis_port = new("analysis_port", this);
    endfunction

    function void write(uvm_logic_vector::sequence_item #(ITEM_WIDTH) t);
        // Writes the port number if an item was read from it
        analysis_port.write(port_number);
    endfunction

endclass
