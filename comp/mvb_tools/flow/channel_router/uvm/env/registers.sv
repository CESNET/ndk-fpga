/*
 * file       : regmodel.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: regmodel for application core
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class reg_dist extends uvm_reg;
    `uvm_object_utils(uvm_channel_router::reg_dist)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field ch_max;
    rand uvm_reg_field ch_min;
    rand uvm_reg_field incr;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build(logic [8-1:0] reset_ch_max, logic [8-1:0] reset_ch_min, logic [8-1:0] reset_ch_incr);
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        ch_max = uvm_reg_field::type_id::create("ch_max");
        ch_min = uvm_reg_field::type_id::create("ch_min");
        incr   = uvm_reg_field::type_id::create("incr");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        ch_max.configure(this, 8, 16, "RW", 0, reset_ch_max, 1, 1, 0);
        ch_min.configure(this, 8, 8 , "RW", 0, reset_ch_min, 1, 1, 0);
        incr.configure(  this, 8, 0 , "RW", 0, reset_ch_incr, 1, 1, 0);
    endfunction
endclass
