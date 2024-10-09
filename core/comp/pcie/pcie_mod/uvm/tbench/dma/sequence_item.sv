// sequence_item.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause

class sequence_item_rq  extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_dma::sequence_item_rq)

    rand uvm_ptc_info::sequence_item hdr;
    rand logic[32-1:0]               data[];

    constraint size_t {
        (hdr.type_ide == 1) ->  data.size() == hdr.length;
        (hdr.type_ide == 0) ->  data.size() == 0;
        hdr.length <= 2**10;
        data.size() <= 15000;
        solve hdr.length before data;
    };

    function new(string name = "");
        super.new(name);
        hdr = uvm_ptc_info::sequence_item::type_id::create({name, ".hdr"});
    endfunction

    function void do_copy(uvm_object rhs);
        sequence_item_rq _rhs;

        $cast(_rhs, rhs);
        hdr.do_copy(_rhs.hdr);
        data = _rhs.data;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        sequence_item_rq _rhs;

        $cast(_rhs, rhs);
        ret &= hdr.do_compare(_rhs.hdr, comparer);
        ret &= (data == _rhs.data);
        return ret;
    endfunction

    function string convert2string();
        string msg = "";

        msg = {hdr.convert2string(), $sformatf("\n\tdata : %p\n", data)};
        return msg;
    endfunction
endclass


class sequence_item_rc  extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_dma::sequence_item_rc)

    int unsigned length;
    int unsigned completed;
    int unsigned tag;
    int unsigned unit_id;
    logic [32-1:0] data[];

    function new(string name = "");
        super.new(name);
    endfunction

        // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item_rc rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        data      = rhs_.data;
        length    = rhs_.length;
        completed = rhs_.completed;
        tag       = rhs_.tag;
        unit_id   = rhs_.unit_id;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item_rc rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= (data      === rhs_.data);
        ret &= (length    === rhs_.length);
        ret &= (completed === rhs_.completed);
        ret &= (tag       === rhs_.tag);
        ret &= (unit_id   === rhs_.unit_id);

        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    function string convert2string_header();
        string msg = "";
        msg = {msg, $sformatf("\n\tDMA RC HEADER : ")};
        msg = {msg, $sformatf("\n\t\tlength %0d\n\t\tcompleted %b", length, completed&1'b1)};
        msg = {msg, $sformatf("\n\t\ttag : %0d(0x%0h)\n\t\tunit_id 0x%h", tag, tag, unit_id)};
        return msg;
    endfunction

    function string convert2string_data();
        string msg = $sformatf("\n\tDMA RC DATA : size(%0d) ", data.size());
        for (int unsigned it = 0; it < data.size(); it++) begin
            if (it % 8 == 0) begin
                msg = {msg, $sformatf("\n\t\t%h", data[it])};
            end else begin
                msg = {msg, $sformatf("  %h", data[it])};
            end
        end
        return msg;
    endfunction

    // Convert transaction into human readable form.
    function string convert2string();
        string msg;
        msg = {this.convert2string_header(), this.convert2string_data()};
        return msg;
    endfunction
endclass

