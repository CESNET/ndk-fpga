//-- monitor.sv: Monitor for logic vector
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class monitor #(int unsigned DATA_WIDTH) extends uvm_monitor;

    `uvm_component_param_utils(uvm_logic_vector::monitor#(DATA_WIDTH))

    // Used to send transactions to all connected components.
    uvm_analysis_port #(sequence_item #(DATA_WIDTH)) analysis_port;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        analysis_port = new("analysis port", this);
    endfunction

endclass

