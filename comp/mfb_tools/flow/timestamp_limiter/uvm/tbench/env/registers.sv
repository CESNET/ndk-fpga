// registers.sv: register model
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class reg_reset_queue extends uvm_reg;
    `uvm_object_utils(uvm_timestamp_limiter::reg_reset_queue)

    // Write
    rand uvm_reg_field ts_lim_reset_queue;

    function new(string name = "reg_reset_queue");
        super.new(name, 1, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        ts_lim_reset_queue = uvm_reg_field::type_id::create("ts_lim_reset_queue");
        //Configure
        ts_lim_reset_queue.configure(this, // Parent
                                 1   , // Number of bits
                                 0   , // LSB
                                 "WO", // Access
                                 0   , // Volatility
                                 0   , // Value on reset
                                 1   , // Can the value be reset?
                                 1   , // Can the value be randomized?
                                 0     // Does the field occupy an entire byte lane?
                                 );
    endfunction
endclass


class reg_sel_queue #(QUEUES) extends uvm_reg;
    `uvm_object_param_utils(uvm_timestamp_limiter::reg_sel_queue #(QUEUES))

    // Write
    rand uvm_reg_field ts_lim_sel_queue;

    function new(string name = "reg_sel_queue");
        super.new(name, QUEUES, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        //Create fields
        ts_lim_sel_queue = uvm_reg_field::type_id::create("ts_lim_sel_queue");
        //Configure
        ts_lim_sel_queue.configure(this   , // Parent
                                 QUEUES   , // Number of bits
                                 0        , // LSB
                                 "RW"     , // Access
                                 0        , // Volatility
                                 0        , // Value on reset
                                 1        , // Can the value be reset?
                                 1        , // Can the value be randomized?
                                 0          // Does the field occupy an entire byte lane?
                                 );
    endfunction
endclass
