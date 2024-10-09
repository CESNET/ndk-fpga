/*
 * file       : regmodel.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: regmodel for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class regmodel extends uvm_reg_block;
    `uvm_object_utils(uvm_app_core::regmodel)

    function new(string name = "reg_block");
        super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
    endfunction

    virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
        `uvm_fatal(this.get_full_name(), "\n\tThis is base register model and should be override!");
        //this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
        //this.lock_model();
    endfunction
endclass

