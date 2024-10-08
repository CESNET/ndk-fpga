//-- config.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class config_item#(DMA_PORTS) extends uvm_object;

    // ------------------------------------------------------------------------
    // configuration variables
    uvm_active_passive_enum active;
    string interface_name;
    logic [$clog2(DMA_PORTS)-1 : 0] port;

    // ------------------------------------------------------------------------
    // functions
    function new (string name = "");
        super.new(name);
    endfunction
endclass
