//-- registers.sv: package with rx_mac_lite register model
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class reg_enable extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_enable)

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
    `uvm_object_utils(uvm_rx_mac_lite::reg_counter)

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


class reg_error extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_error)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field adapter_error;
    rand uvm_reg_field crc_error;
    rand uvm_reg_field min_mtu_check;
    rand uvm_reg_field mtu_check;
    rand uvm_reg_field mac_check;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        adapter_error = uvm_reg_field::type_id::create("adapter_error");
        crc_error     = uvm_reg_field::type_id::create("crc_error");
        min_mtu_check = uvm_reg_field::type_id::create("min_mtu_check");
        mtu_check     = uvm_reg_field::type_id::create("mtu_check");
        mac_check     = uvm_reg_field::type_id::create("mac_check");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        //configure(uvm_reg parent, size, lsb_pos, access, volatile, reset, has_reset, is_rand, individually_accessible);
        adapter_error.configure(this, 1, 0, "RW", 1, 'h0, 1, 0, 0);
        crc_error    .configure(this, 1, 1, "RW", 1, 'h0, 1, 0, 0);
        min_mtu_check.configure(this, 1, 2, "RW", 1, 'h0, 1, 0, 0);
        mtu_check    .configure(this, 1, 3, "RW", 1, 'h0, 1, 0, 0);
        mac_check    .configure(this, 1, 4, "RW", 1, 'h0, 1, 0, 0);
    endfunction
endclass


class reg_status extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_status)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field mfifo_ovf;
    rand uvm_reg_field dfifo_ovf;
    rand uvm_reg_field debug;

    rand uvm_reg_field link_status;

    rand uvm_reg_field inbandfcs;
    rand uvm_reg_field mac_count;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        mfifo_ovf   = uvm_reg_field::type_id::create("mfifo_ovf");
        dfifo_ovf   = uvm_reg_field::type_id::create("dfifo_ovf");
        debug       = uvm_reg_field::type_id::create("debug");
        link_status = uvm_reg_field::type_id::create("link_status");
        inbandfcs   = uvm_reg_field::type_id::create("inbandfcs");
        mac_count   = uvm_reg_field::type_id::create("mac_count");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        //configure(uvm_reg parent, size, lsb_pos, access, volatile, reset, has_reset, is_rand, individually_accessible);
        mfifo_ovf  .configure(this, 1,  0, "RW", 1, 'h0, 1, 0, 0);
        dfifo_ovf  .configure(this, 1,  1, "RW", 1, 'h0, 1, 0, 0);
        debug      .configure(this, 2,  2, "RW", 1, 'h0, 1, 0, 0);
        link_status.configure(this, 1,  7, "RO", 1, 'h0, 1, 0, 0);
        inbandfcs  .configure(this, 1, 22, "RO", 1, 'h0, 1, 0, 0);
        mac_count  .configure(this, 5, 23, "RO", 1, 'h0, 1, 0, 0);
    endfunction
endclass

class reg_command extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_command)

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


class reg_length extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_length)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field max;

    function new(string name = "reg_length");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        max = uvm_reg_field::type_id::create("max");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        max.configure(this, 16, 0, "RW", 0, 'h0, 1, 0, 0);
    endfunction
endclass


class reg_mtu extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_mtu)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field length;

    function new(string name = "reg_mac_check");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build(int unsigned def_value);
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        length = uvm_reg_field::type_id::create("length");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        length.configure(this, 32, 0, "RW", 0, def_value, 1, 0, 0);
    endfunction
endclass

class reg_mac_check extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_mac_check)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field enable;

    function new(string name = "reg_mac_check");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        enable = uvm_reg_field::type_id::create("enable");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        enable.configure(this, 2, 0, "RW", 0, 'h0, 1, 0, 0);
    endfunction
endclass

class reg_mac extends uvm_reg;
    `uvm_object_utils(uvm_rx_mac_lite::reg_mac)

    //rand uvm_reg_field rsvd; //RESERVED
    rand uvm_reg_field map;
    rand uvm_reg_field vld;

    function new(string name = "reg_mac_check");
        super.new(name, 64, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        //rsvd   = uvm_reg_field::type_id::create("rsvd");
        map = uvm_reg_field::type_id::create("map");
        vld = uvm_reg_field::type_id::create("vld");

        //Configure
        //rsvd.configure(  this, 8, 24, "RW", 0, 8'h00, 1, 1, 0);
        map.configure(this, 48, 0, "RW", 0, 'h0, 1, 0, 0);
        vld.configure(this, 1, 48, "RW", 0, 'h0, 1, 0, 0);
    endfunction
endclass


