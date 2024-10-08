// registers.sv: Registers module
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

class status_register extends uvm_reg;
    `uvm_object_utils(uvm_rate_limiter::status_register)

    uvm_reg_field idle;
    uvm_reg_field conf;
    uvm_reg_field run;
    uvm_reg_field wr_aux;
    uvm_reg_field ptr_rst;
    uvm_reg_field shaping;

    function new(string name = "reg_status");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    function void build();
        idle    = uvm_reg_field::type_id::create("idle");
        conf    = uvm_reg_field::type_id::create("conf");
        run     = uvm_reg_field::type_id::create("run");
        wr_aux  = uvm_reg_field::type_id::create("wr_aux");
        ptr_rst = uvm_reg_field::type_id::create("ptr_rst");
        shaping = uvm_reg_field::type_id::create("shaping");

        //                 parent, bits, lsb, access, volatile?, reset value, reset?, random?, byte?
        idle.configure(    this  , 1   , 0  , "RO"  , 0        , 1          , 1     , 0      , 0     );
        conf.configure(    this  , 1   , 1  , "RW"  , 0        , 0          , 1     , 0      , 0     );
        run.configure(     this  , 1   , 2  , "RW"  , 0        , 0          , 1     , 0      , 0     );
        wr_aux.configure(  this  , 1   , 3  , "RW"  , 0        , 0          , 1     , 0      , 0     );
        ptr_rst.configure( this  , 1   , 4  , "RW"  , 0        , 0          , 1     , 0      , 0     );
        shaping.configure( this  , 1   , 5  , "RW"  , 0        , 0          , 1     , 0      , 0     );
    endfunction
endclass

class data_register extends uvm_reg;
    `uvm_object_utils(uvm_rate_limiter::data_register)

    uvm_reg_field data;

    function new(string name = "reg_data");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build(string access = "RW", unsigned rst_val = 32, bit reset = 1);
        data = uvm_reg_field::type_id::create("data");
        data.configure(this, 32, 0, access, 0, rst_val, reset, 0, 1);
    endfunction
endclass
