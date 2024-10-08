/*
 * file       : sequence_item.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mi sequence_item request and response
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

////////////////////////////////////////////////////////////////////////
// MI REQUEST
////////////////////////////////////////////////////////////////////////
class sequence_item_request #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_common::sequence_item;

    // registration of object tools
    `uvm_object_param_utils(uvm_mi::sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    //variables
    rand logic [ADDR_WIDTH-1:0]   addr;
    rand logic [META_WIDTH-1:0]   meta;
    rand logic [DATA_WIDTH/8-1:0] be;

    rand logic wr;
    rand logic [DATA_WIDTH-1:0] dwr;

    rand logic rd;

    logic ardy;

    //RD and WR cannot be both in asserted
    constraint c_rd_wr {
        !(wr && rd);
    }

     //Constructor
    function new(string name = "mem_seq_item");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "mi::sequence_item_request::do_copy ", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes.
        super.do_copy(rhs);
        addr = rhs_.addr;
        be   = rhs_.be;
        wr   = rhs_.wr;
        dwr  = rhs_.dwr;
        meta  = rhs_.meta;
        rd   = rhs_.rd;
        ardy = rhs_.ardy;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) rhs_;
        bit ret;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("mi::sequence_item_request::do_compare", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= (addr === rhs_.addr);
        ret &= (be   === rhs_.be);
        ret &= (wr   === rhs_.wr);
        if (wr == 1'b1) begin
            for (int unsigned it = 0; it < DATA_WIDTH/8; it++) begin
                if (be[it] == 1'b1) begin
                    ret &= (dwr[(it+1)*8 -: 8]  === rhs_.dwr[(it+1)*8 -: 8]);
                end
            end
        end
        ret &= (meta  === rhs_.meta);
        ret &= (rd    === rhs_.rd);
        ret &= (ardy  === rhs_.ardy);
        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string s = "";

        $sformat(s, {"MI REQUEST :\n\taddr: h%0h\n\tBE: '%b\n\twrite %b\n\tdwr: 'h%0h\n\tmeta: 'h%0h\n\tread %b\n\tardy %b\n"},
            addr,
            be,
            wr,
            dwr,
            meta,
            rd,
            ardy
            );
        return s;
    endfunction: convert2string
endclass

////////////////////////////////////////////////////////////////////////
// MI RESPONSE
////////////////////////////////////////////////////////////////////////
class sequence_item_response #(int unsigned DATA_WIDTH) extends uvm_common::sequence_item;

    // registration of object tools
    `uvm_object_param_utils(uvm_mi::sequence_item_response#(DATA_WIDTH))

    //variables
    //logic [DATA_WIDTH/8-1:0] be; // for comaring data
    rand logic [DATA_WIDTH-1:0] drd;
    rand logic ardy;
    rand logic drdy;

    function new(string name = "sequence_item_response");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        sequence_item_response #(DATA_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "mi::sequence_item_response::do_copy ", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes.
        super.do_copy(rhs);
        drd  = rhs_.drd;
        ardy = rhs_.ardy;
        drdy = rhs_.drdy;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item_response #(DATA_WIDTH) rhs_;
        bit ret;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("mi::sequence_item_response::do_compare", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= (drd  === rhs_.drd);
        ret &= (ardy === rhs_.ardy);
        ret &= (drdy === rhs_.drdy);
        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string s = "";

        $sformat(s, {"MI RESPONSE :\n\tdrd: h%0h\n\tardy: %b\n\tdrdy %b"},
            drd,
            ardy,
            drdy
            );
        return s;
    endfunction: convert2string
endclass
