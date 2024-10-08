/*
 * file       : ipg_generator.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM object, which generates inter packet gap and appends
 *              it to end of data, which should be wrapped by preamble and end of frame
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class ipg_gen extends uvm_object;
    `uvm_object_utils(uvm_byte_array_mii::ipg_gen);

    local int unsigned idle_count_min;
    local int unsigned idle_count_max;

    //  Group: Variables
    rand int unsigned idle_count;

    constraint idle_count_constr {
        idle_count inside {[idle_count_min : idle_count_max]};
    }

    //  Constructor: new
    function new(string name = "ipg_generator", int unsigned idle_count_min = 4096, int unsigned idle_count_max = 4*4096);
        super.new(name);

        MIN_IPG : assert(idle_count_min >= MIN_IPG_SIZE);
        this.idle_count_min = idle_count_min;
        this.idle_count_max = idle_count_max;
    endfunction: new

    //  Group: Functions

    // Appends random count of IDLE character to message to created desired
    // inter packet gap (IPG)
    function void generate_ipg(ref byte unsigned data[$], ref logic control[$]);
        this.randomize();

        for (int i = 0; i < idle_count; i++) begin
            data.push_back(8'h07);
            control.push_back(1'b1);
        end
    endfunction

endclass: ipg_gen
