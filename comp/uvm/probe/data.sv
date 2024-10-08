/*
 * file       : data.sv
 * Copyright (C) 2023 CESNET z. s. p. o.
 * description: event data
 * date       : 2023
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class data#(int unsigned DATA_WIDTH) extends uvm_object;
    `uvm_object_param_utils(uvm_probe::data#(DATA_WIDTH))

    logic [DATA_WIDTH-1:0] data;

    function new(string name = "");
        super.new(name);
    endfunction

endclass
