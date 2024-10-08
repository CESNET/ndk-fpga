/*
 * file       : registers.sv
 * description: Registers for MAC Lites
 * date       : 2022
 * author     : Daniel Kondys <xkondy00@vutbr.cz>
 *
 * Copyright (C) 2022 CESNET z. s. p. o.
*/

class mac_control extends uvm_reg;
    `uvm_object_utils(net_mod_logic_env::mac_control)

    // Write
    rand uvm_reg_field enable;

    function new(string name = "reg_status");
        super.new(name, 1, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        enable = uvm_reg_field::type_id::create("enable");

        //Configure
        enable.configure( this, // Parent
                          1   , // Number of bits
                          0   , // LSB
                          "RW", // Access
                          0   , // Volatility
                          0   , // Value on reset
                          1   , // Can the value be reset?
                          0   , // Can the value be randomized?
                          0     // Does the field occupy an entire byte lane? 
                               );
        
    endfunction
endclass
