// sequence_item.sv
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_item_rq  extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_dma::sequence_item_rq)

    //rand uvm_ptc_info::sequence_item hdr;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_LENGTH_W-1 : 0]  length;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_TYPE_W-1 : 0]    type_ide;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_FIRSTIB_W-1 : 0] firstib;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_LASTIB_W-1 : 0]  lastib;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_TAG_W-1 : 0]     tag;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_UNITID_W-1 : 0]  unitid;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_GLOBAL_W-1 : 0]  global_id;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_VFID_W-1 : 0]    vfid;
    rand logic                                                pasid;
    rand logic                                                pasidvld;
    rand logic [sv_dma_bus_pack::DMA_REQUEST_RELAXED_W-1 : 0] relaxed;
    rand logic[32-1:0]               data[];

    constraint size_t {
        (type_ide == 1) ->  data.size() == length;
        (type_ide == 0) ->  data.size() == 0;
        length      <= 2**sv_dma_bus_pack::DMA_REQUEST_LENGTH_W;
        data.size() <= 2**sv_dma_bus_pack::DMA_REQUEST_LENGTH_W;
        solve length before data;
    };

    function new(string name = "");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        sequence_item_rq _rhs;

        $cast(_rhs, rhs);
        super.copy(rhs);
        length    = _rhs.length;
        type_ide  = _rhs.type_ide;
        firstib   = _rhs.firstib;
        lastib    = _rhs.lastib;
        tag       = _rhs.tag;
        unitid    = _rhs.unitid;
        global_id = _rhs.global_id;
        vfid      = _rhs.vfid;
        pasid     = _rhs.pasid;
        pasidvld  = _rhs.pasidvld;
        relaxed   = _rhs.relaxed;
        data = _rhs.data;
    endfunction

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        sequence_item_rq _rhs;

        $cast(_rhs, rhs);
        ret = super.compare(rhs);
        ret &= (length    === _rhs.length);
        ret &= (type_ide  === _rhs.type_ide);
        ret &= (firstib   === _rhs.firstib);
        ret &= (lastib    === _rhs.lastib);
        ret &= (tag       === _rhs.tag);
        ret &= (unitid    === _rhs.unitid);
        ret &= (global_id === _rhs.global_id);
        ret &= (vfid      === _rhs.vfid);
        ret &= (pasid     === _rhs.pasid);
        ret &= (pasidvld  === _rhs.pasidvld);
        ret &= (relaxed   === _rhs.relaxed);
        ret &= (data === _rhs.data);
        return ret;
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

    function string convert2string();
        string msg = "";

        msg = this.time2string();
        msg = {msg, $sformatf("\tLength : %d\n\tType : %b\n\tFirstIB : %0d\n\tlastIB : %0d\n\ttag : %0d(0x%h)\n\tunitid : 0x%h\n\tglobal : 0x%h\n\tvfid : 0x%h\n\tpasid : 0x%h\n\tpasidvld : %b\n\trelaxed : %b\n",
                     length != 0 ? length : 1024, type_ide, firstib, lastib, tag, tag, unitid, global_id, vfid, pasid, pasidvld, relaxed)};
        msg = {msg, convert2string_data()};
        return msg;
    endfunction
endclass


class sequence_item_rc  extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_dma::sequence_item_rc)

    int unsigned length;
    logic        completed;
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
        msg = {msg, $sformatf("\n\t\tlength %0d\n\t\tcompleted %b", length, completed)};
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

