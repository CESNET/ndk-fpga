//-- monitor.sv: Monitor for MVB environment
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class mi_subscriber #(MI_DATA_WIDTH, MI_ADDR_WIDTH) extends uvm_subscriber#(uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0));
    `uvm_component_param_utils(uvm_mtc::mi_subscriber #(MI_DATA_WIDTH, MI_ADDR_WIDTH))

    // Analysis port
    uvm_analysis_port #(uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0)) port;

    function new (string name, uvm_component parent = null);
        super.new(name, parent);
        port = new("port", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    virtual function void write(uvm_mi::sequence_item_request #(MI_DATA_WIDTH, MI_ADDR_WIDTH, 0) t);
        if (t.ardy && (t.wr || t.rd)) begin
            port.write(t);
        end
    endfunction
endclass
