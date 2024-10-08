/*
 * file       : env_config.sv
 * description: config to reset sychronization enviroment
 * Copyright (C) 2021 CESNET z. s. p. o.
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class env_config_item #(int unsigned RESETS) extends uvm_object;

    ////////////////
    // configuration variables
    uvm_active_passive_enum active[RESETS];
    string interface_name[RESETS];
    time   driver_delay;

    ////////////////
    // functions
    function new (string name = "");
        super.new(name);
        driver_delay = 40ns;
        for (int unsigned it = 0; it < RESETS; it++) begin
            active[it] = UVM_ACTIVE;
        end
    endfunction
endclass

