//-- registers.sv: package with rx_mac_lite register model
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class reg_enable extends uvm_reg;
    `uvm_object_utils(uvm_tx_mac_lite::reg_enable)

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

class reg_counter extends uvm_reg;
    `uvm_object_utils(uvm_tx_mac_lite::reg_counter)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field value;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        value = uvm_reg_field::type_id::create("value");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        //configure(uvm_reg parent, size, lsb_pos, access, volatile, reset, has_reset, is_rand, individually_accessible);
        value.configure(this, 32, 0, "RO", 1, 'h0, 1, 0, 0);
    endfunction
endclass

class reg_command extends uvm_reg;
    `uvm_object_utils(uvm_tx_mac_lite::reg_command)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field command;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        command = uvm_reg_field::type_id::create("command");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        command.configure(this, 8, 0, "WO", 0, 'h0, 1, 0, 0);
    endfunction
endclass


class reg_status extends uvm_reg;
    `uvm_object_utils(uvm_tx_mac_lite::reg_status)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field enable;
    rand uvm_reg_field crc_insert;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        enable       = uvm_reg_field::type_id::create("enable");
        crc_insert   = uvm_reg_field::type_id::create("crc_insert");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        //configure(uvm_reg parent, size, lsb_pos, access, volatile, reset, has_reset, is_rand, individually_accessible);
        enable    .configure(this, 1,  0, "RO", 1, 'h0, 1, 0, 0);
        crc_insert.configure(this, 1,  1, "RO", 1, 'h0, 1, 0, 0);
    endfunction
endclass
