/*
 * file       : sequence_item.sv
 * Copyright (C) 2024 CESNET z. s. p. o.
 * description: base sequence_item which provide some added function. (ADDED time when packet have been received)
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


virtual class sequence_item extends uvm_sequence_item;

    // Monitor can write his name and data
    /*protected*/ time start[string];

    /*deprecated (old compatibility) */ string tag;

    function new(string name = "sequence_item");
        super.new(name);
        start.delete();
    endfunction

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        start = start;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        //dont compare start variable it is only informational
        return super.do_compare(rhs, comparer);
    endfunction: do_compare

    function string time2string(string prefix = "\n\t");
        string ret = "";

        foreach (start[it]) begin
            ret = {ret, prefix, it, " : ", $sformatf("%0dns", start[it]/1ns)};
        end

        return ret;
    endfunction

    // Convert transaction into human readable form.
    function string convert2string();
        string ret = "\n";
        ret = super.convert2string();

        ret = {ret, time2string()};
        return ret;
    endfunction

    function void time_add(string name, time t);
        start[name] = t;
    endfunction

    function void time_array_add(time input_time[string]);
        foreach (input_time[it]) begin
            start[it] = input_time[it];
        end
    endfunction

    function time time_last();
        time ret = 0ns;
        foreach (start[it]) begin
            if (ret < start[it]) begin
                ret = start[it];
            end
        end
        return ret;
    endfunction
endclass

