// registers.sv: Definitions for single registers
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Válek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class control_register extends uvm_reg;
    `uvm_object_utils(uvm_tx_dma_calypte_regs::control_register)

    // Write
    rand uvm_reg_field dma_enable;

    function new(string name = "control_register");
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
    `uvm_object_utils(uvm_tx_dma_calypte_regs::status_register)

    // Write
    rand uvm_reg_field dma_status;

    function new(string name = "status_register");
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
    `uvm_object_utils(uvm_tx_dma_calypte_regs::pointer_register)

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

class pointer_mask_register extends uvm_reg;
    `uvm_object_utils(uvm_tx_dma_calypte_regs::pointer_mask_register)

    // Write
    rand uvm_reg_field pointer;

    function new(string name = "pointer_mask_register");
        super.new(name, 16, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        pointer = uvm_reg_field::type_id::create("pointer_mask");
        //Configure
        pointer.configure(this, // Parent
                         16   , // Number of bits
                         0  , // LSB
                         "RO", // Access
                         0   , // Volatility
                         0   , // Value on reset
                         0   , // Can the value be reset?
                         0   , // Can the value be randomized?
                         0     // Does the field occupy an entire byte lane?
                         );
    endfunction
endclass

class cnt_register extends uvm_reg;
    `uvm_object_utils(uvm_tx_dma_calypte_regs::cnt_register)

    // Write
    rand uvm_reg_field cnt;

    function new(string name = "cnt_register");
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
