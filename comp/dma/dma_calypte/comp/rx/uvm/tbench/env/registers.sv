//-- registers.sv: register model
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class control_register extends uvm_reg;
    `uvm_object_utils(uvm_dma_ll::control_register)

    // Write
    rand uvm_reg_field dma_enable;

    function new(string name = "reg_status");
        super.new(name, 1, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        dma_enable = uvm_reg_field::type_id::create("dma_enable");
        //Configure
        dma_enable.configure(this, // Parent
                                 1   , // Number of bits
                                 0   , // LSB
                                 "RW", // Access
                                 0   , // Volatility
                                 0   , // Value on reset
                                 1   , // Can the value be reset?
                                 1   , // Can the value be randomized?
                                 0     // Does the field occupy an entire byte lane?
                                 );
    endfunction
endclass


class status_register extends uvm_reg;
    `uvm_object_utils(uvm_dma_ll::status_register)

    // Write
    rand uvm_reg_field dma_status;

    function new(string name = "reg_status");
        super.new(name, 1, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        dma_status = uvm_reg_field::type_id::create("dma_status");
        //Configure
        dma_status.configure(this, // Parent
                                 1   , // Number of bits
                                 0  , // LSB
                                 "RO", // Access
                                 0   , // Volatility
                                 0   , // Value on reset
                                 1   , // Can the value be reset?
                                 1   , // Can the value be randomized?
                                 0     // Does the field occupy an entire byte lane?
                                 );
    endfunction
endclass


class pointer_register extends uvm_reg;
    `uvm_object_utils(uvm_dma_ll::pointer_register)

    // Write
    rand uvm_reg_field pointer;

    function new(string name = "pointer_register");
        super.new(name, 16, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        pointer = uvm_reg_field::type_id::create("pointer");
        //Configure
        pointer.configure(this, // Parent
                         16   , // Number of bits
                         0  , // LSB
                         "RW", // Access
                         0   , // Volatility
                         0   , // Value on reset
                         1   , // Can the value be reset?
                         1   , // Can the value be randomized?
                         0     // Does the field occupy an entire byte lane?
                         );
    endfunction
endclass


class addr_register extends uvm_reg;
    `uvm_object_utils(uvm_dma_ll::addr_register)

    // Write
    rand uvm_reg_field addr;

    function new(string name = "addr_register");
        super.new(name, 64, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        addr = uvm_reg_field::type_id::create("addr");
        //Configure
        addr.configure(this, // Parent
                       64   , // Number of bits
                       0  , // LSB
                       "RW", // Access
                       0   , // Volatility
                       0   , // Value on reset
                       1   , // Can the value be reset?
                       1   , // Can the value be randomized?
                       0     // Does the field occupy an entire byte lane?
                       );
    endfunction
endclass


class cnt_register extends uvm_reg;
    `uvm_object_utils(uvm_dma_ll::cnt_register)

    // Write
    rand uvm_reg_field cnt;

    function new(string name = "cnt");
        super.new(name, 64, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        cnt = uvm_reg_field::type_id::create("cnt");
        //Configure
        cnt.configure(this, // Parent
                      64   , // Number of bits
                      0  , // LSB
                      "RO", // Access
                      0   , // Volatility
                      0   , // Value on reset
                      1   , // Can the value be reset?
                      1   , // Can the value be randomized?
                      0     // Does the field occupy an entire byte lane?
                      );
    endfunction
endclass



