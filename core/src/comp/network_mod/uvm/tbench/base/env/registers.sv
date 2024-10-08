//-- regmodel.sv  registre model
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class reg_enable extends uvm_reg;
    `uvm_object_utils(uvm_network_mod_env::reg_enable)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field enable;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        enable = uvm_reg_field::type_id::create("enable");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        enable.configure(this, 1, 0, "RW", 0, 'h0, 1, 0, 0);
    endfunction
endclass


