/*
 * file       : sequence_item.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: RESET sequence item
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_item #(int unsigned SEGMENTS) extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_intel_mac_seg::sequence_item#(SEGMENTS));

    rand logic [64-1:0] data[SEGMENTS];
    rand logic          inframe[SEGMENTS];
    rand logic [3-1:0]  eop_empty[SEGMENTS];
    rand logic          fcs_error[SEGMENTS];
    rand logic [2-1:0]  error[SEGMENTS];
    rand logic [3-1:0]  status_data[SEGMENTS];
    rand logic          valid;
    rand logic          ready;


    function new (string name = "sequence_item");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        sequence_item #(SEGMENTS) c_rhs;

        super.do_copy(rhs);
        $cast(c_rhs, rhs);

        data        = c_rhs.data;
        inframe     = c_rhs.inframe;
        eop_empty   = c_rhs.eop_empty;
        fcs_error   = c_rhs.fcs_error;
        error       = c_rhs.error;
        status_data = c_rhs.status_data;
        valid       = c_rhs.valid;
        ready       = c_rhs.ready;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item #(SEGMENTS) c_rhs;

        ret = super.do_compare(rhs, comparer);
        $cast(c_rhs, rhs);

        ret &= (data        == c_rhs.data);
        ret &= (inframe     == c_rhs.inframe);
        ret &= (eop_empty   == c_rhs.eop_empty);
        ret &= (fcs_error   == c_rhs.fcs_error);
        ret &= (error       == c_rhs.error);
        ret &= (status_data == c_rhs.status_data);
        ret &= (valid       == c_rhs.valid);
        ret &= (ready       == c_rhs.ready);
        return ret;
    endfunction

    function string convert2string();
        string s = "";
        s = $sformatf("intel_seq_mac::sequence_item valid %d ready %d\n\t", valid, ready);
        for (int unsigned it = 0; it < SEGMENTS; it++) begin
            s = {s, $sformatf("Item %d:\n\t\tDATA : %h\n\t\tinframe %b\n\t\teop_empty %d\n\t\t, fcs_error : %b\n\t\terror : %b\n\t\t status data: %b\n",
                    it, data[it], inframe[it], eop_empty[it], fcs_error[it], error[it], status_data[it])};
        end
       return s;
    endfunction
endclass

