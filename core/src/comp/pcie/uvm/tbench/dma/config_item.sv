// config_item.sv: configuration item for dma interface
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class config_item extends uvm_object;

    // ------------------------------------------------------------------------
    // Configuration variables
    string interface_name_rq_mfb;
    string interface_name_rq_mvb;
    string interface_name_rc_mfb;
    string interface_name_rc_mvb;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name = "");
        super.new(name);
    endfunction

endclass


