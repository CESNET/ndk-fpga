// header.sv: PCIE header 
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause

// This class represents high level transaction, which can be reusable for other components.
class header extends uvm_common::sequence_item;
    // Registration of object tools.
    `uvm_object_utils(uvm_pcie::header)

    enum {RQ_HDR, COMPLETER_HDR} hdr_type;
    rand logic [3-1:0]  fmt;
    rand logic [5-1:0]  pcie_type;
    rand logic [3-1:0]  traffic_class;
    rand logic [1-1:0]  id_based_ordering; //
    rand logic [1-1:0]  relaxed_ordering; //
    rand logic [1-1:0]  no_snoop; //
    rand logic [1-1:0]  th; // TLP Processing Hints
    rand logic [1-1:0]  td;
    rand logic [1-1:0]  ep; // poisoned
    rand logic [2-1:0]  at;
    rand logic [10-1:0] length; //dwords
    rand logic [32-1:0] data[];

    constraint data_const {
        fmt[3-1:1] == 2'b01 -> (length == 0 -> (data.size() == 1024));
        fmt[3-1:1] == 2'b01 -> (length != 0 -> (data.size() == length));
        fmt[3-1:1] == 2'b00 -> (data.size() == 0);
        data.size() inside {[0:1024]};

        solve fmt    before data;
        solve length before data;
    }


    function new(string name = "header");
        super.new(name);
    endfunction

    function int unsigned length_get();
        return length != 0 ? length : 1024;
    endfunction

   // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        header rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        hdr_type      = rhs_.hdr_type;
        fmt           = rhs_.fmt;
        pcie_type     = rhs_.pcie_type;
        traffic_class = rhs_.traffic_class;
        id_based_ordering = rhs_.id_based_ordering;
        relaxed_ordering  = rhs_.relaxed_ordering;
        no_snoop          = rhs_.no_snoop;
        th            = rhs_.th; // TLP Processing Hints
        td            = rhs_.td;
        ep            = rhs_.ep; // poisoned
        at            = rhs_.at;
        length        = rhs_.length; //dwords
    endfunction: do_copy

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        header rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret &= fmt       === rhs_.fmt;
        ret &= pcie_type === rhs_.pcie_type;
        ret &= traffic_class === rhs_.traffic_class;
        ret &= id_based_ordering === rhs_.id_based_ordering;
        ret &= relaxed_ordering  === rhs_.relaxed_ordering;
        ret &= no_snoop          === rhs_.no_snoop;
        ret &= th            === rhs_.th; // TLP Processing Hints
        ret &= td            === rhs_.td;
        ret &= ep            === rhs_.ep; // poisoned
        ret &= at            === rhs_.at;
        ret &= length        === rhs_.length; //dwords
        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    function string convert_data2string();
        string msg;

        for (int unsigned it = 0; it < data.size(); it++) begin
            if (it % 8 == 0) begin
                msg = {msg, $sformatf("\n\t%h", data[it])};
            end else begin
                msg = {msg, $sformatf("  %h", data[it])};
            end
        end
        return msg;
    endfunction


    function string convert2string();
        string msg;

        msg = super.convert2string();
        msg = {msg, $sformatf("\nheader type %s\n", hdr_type)};
        msg = {msg, $sformatf("\tfmt : 0x%h type : 0x%h trafic_class : 0x%h\n", fmt, pcie_type[5-1:0], traffic_class)};
        msg = {msg, $sformatf("\t(id_ordering, relax_ordering, no_snoop   : %b,%b,%b\n", id_based_ordering, relaxed_ordering, no_snoop)};
        msg = {msg, $sformatf("\t(th, td, ep   : %b,%b,%b\n", th, td, ep)};
        msg = {msg, $sformatf("\tat : 0x%h length %0d", at, length != 0 ? length : 1024)};
        return msg;
    endfunction
endclass


class request_header extends header;
    // Registration of object tools.
    `uvm_object_utils(uvm_pcie::request_header)

    rand logic [16-1:0] requester_id;
    rand logic [8-1:0]  tag;
    rand logic [4-1:0]  lbe;
    rand logic [4-1:0]  fbe;
    rand logic [64-1:2] address;
    rand logic [2-1:0]  ph;

    constraint addr_widht {
        fmt[0] == 0 -> address[64-1:32] == 32'b0;
    }

    function new(string name = "sequence_item");
        super.new(name);
        hdr_type = RQ_HDR;
    endfunction

   // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        request_header rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        requester_id = rhs_.requester_id;
        tag        = rhs_.tag;
        lbe        = rhs_.lbe;
        fbe        = rhs_.fbe;
        address    = rhs_.address;
        ph         = rhs_.ph;
    endfunction: do_copy



    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        request_header rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= requester_id === rhs_.requester_id;
        ret &= tag        === rhs_.tag;
        ret &= lbe        === rhs_.lbe;
        ret &= fbe        === rhs_.fbe;
        ret &= address    === rhs_.address;
        ret &= ph         === rhs_.ph;
        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    function string convert2string();
        string msg = super.convert2string();
        msg = {msg, $sformatf("\trequester id : 0x%h tag : %0d(0x%h)\n\tfbe : b%b lbe : b%b\n\taddress : 0x%h ph 0x%h", requester_id, tag, tag, fbe, lbe, {address, 2'b00}, ph)};
        msg = {msg, this.convert_data2string()};
        return msg;
    endfunction
endclass


class completer_header extends header;
    // Registration of object tools.
    `uvm_object_utils(uvm_pcie::completer_header)

    rand logic [16-1:0] completer_id;
    rand logic [3-1:0]  compl_status;
    rand logic [1-1:0]  bcm;
    rand logic [12-1:0] byte_count;
    rand logic [16-1:0] requester_id;
    rand logic [8-1:0]  tag;
    rand logic [7-1:0]  lower_address;

    constraint fmt_const {
        fmt[0] == 0;
    }

    function new(string name = "completer_header");
        super.new(name);
        hdr_type = COMPLETER_HDR;
    endfunction

   // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        completer_header rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        completer_id  = rhs_.completer_id;
        compl_status  = rhs_.compl_status;
        bcm           = rhs_.bcm;
        byte_count    = rhs_.byte_count;
        requester_id  = rhs_.requester_id;
        tag           = rhs_.tag;
        lower_address = rhs_.lower_address;
    endfunction: do_copy

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        completer_header rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= completer_id  === rhs_.completer_id;
        ret &= compl_status  === rhs_.compl_status;
        ret &= bcm           === rhs_.bcm;
        ret &= byte_count    === rhs_.byte_count;
        ret &= requester_id  === rhs_.requester_id;
        ret &= tag           === rhs_.tag;
        ret &= lower_address === rhs_.lower_address;
        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    function string convert2string();
        string msg = super.convert2string();
        msg = {msg, $sformatf("\n\tcompleter id : 0x%h status : 0x%h\n\tbcm : 0%b\n\tbyte_count : %0d", completer_id, compl_status, bcm, byte_count)};
        msg = {msg, $sformatf("\n\trequester id : 0x%h tag : %0d(0x%0h)\n\tlower_address 0x%h", requester_id, tag, tag, lower_address)};
        msg = {msg, this.convert_data2string()};
        return msg;
    endfunction
endclass


