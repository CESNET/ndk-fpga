//-- config.sv:  
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class config_item extends uvm_object;

    // ------------------------------------------------------------------------
    // Configuration variables
    uvm_active_passive_enum active;

    //Config driver
    int unsigned diff_min;
    int unsigned diff_max;
    int unsigned diff_count_min;
    int unsigned diff_count_max;
    int unsigned weigth_mvb_first;
    int unsigned weigth_mfb_first;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name = "");
        super.new(name);
        diff_min = 1;
        diff_max = 2000;
        diff_count_min =  10;
        diff_count_max = 2000;
        weigth_mvb_first = 80;
        weigth_mfb_first = 20;
    endfunction

endclass

