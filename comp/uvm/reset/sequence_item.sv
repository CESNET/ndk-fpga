/*
 * file       : sequence_item.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET sequence item
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_item extends uvm_sequence_item;
    `uvm_object_utils(uvm_reset::sequence_item);

    rand logic reset;

    function new (string name = "sequence_item");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        sequence_item c_rhs;

        super.do_copy(rhs);
        $cast(c_rhs, rhs);
        reset = c_rhs.reset;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item c_rhs;

        ret = super.do_compare(rhs, comparer);
        $cast(c_rhs, rhs);
        ret &= (reset == c_rhs.reset);
        return ret;
    endfunction

    function string convert2string();
        string s = "";

        $sformat (s, "RESET : %b", reset);
        return s;
    endfunction
endclass
