/*
 * file       : transaction.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequence item
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LII_SEQUENCE_ITEM_SV
`define LII_SEQUENCE_ITEM_SV
// This class represents transaction which contains values of output signals for eth phy
class sequence_item #(int unsigned DATA_WIDTH, int unsigned META_WIDTH, int unsigned SOF_WIDTH) extends uvm_common::sequence_item;

    // registration of object tools
    `uvm_object_param_utils(uvm_lii_rx::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH))

    localparam BYTES_VLD_LENGTH = $clog2(DATA_WIDTH/8)+1;

    // Member attributes, equivalent with interface pins
    // make input attributes random, except for clocks
    rand logic [DATA_WIDTH-1 : 0]       data;
    rand logic [BYTES_VLD_LENGTH-1 : 0] bytes_vld;
    rand logic [SOF_WIDTH-1 : 0]        sof;
    rand logic                          eof;
    rand logic                          rdy;
    rand logic                          eeof;
    rand logic [BYTES_VLD_LENGTH-1 : 0] edb;
    rand logic                          link_status;
    rand logic                          err;
    rand logic                          rxseqerr;
    rand logic                          rxblkerr;
    rand logic                          rxidle;
    rand logic                          rxrmterr;
    rand logic                          rxlocerr;
    rand logic                          crc_ok;
    rand logic                          crc_vld;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction: new

    // ------------------------
    // Common UVM functions
    // ------------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object." )
            return;
        end
        // Now copy all attributes.
        super.do_copy(rhs);
        data        = rhs_.data;
        bytes_vld   = rhs_.bytes_vld;
        sof         = rhs_.sof;
        eof         = rhs_.eof;
        rdy         = rhs_.rdy;
        eeof        = rhs_.eeof;
        edb         = rhs_.edb;
        link_status = rhs_.link_status;
        err         = rhs_.err;
        rxseqerr    = rhs_.rxseqerr;
        rxblkerr    = rhs_.rxblkerr;
        rxidle      = rhs_.rxidle;
        rxrmterr    = rhs_.rxrmterr;
        rxlocerr    = rhs_.rxlocerr;
        crc_ok      = rhs_.crc_ok;
        crc_vld     = rhs_.crc_vld;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Using simple equivalence operator (faster).
        return (super.do_compare(rhs, comparer) &&
            (data == rhs_.data));
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string s = "";

        $sformat(s, {
            "%s\n",
            "data: h%0h\n",
            "bytes_vld: h%0h\n",
            "sof:  b%0b\n",
            "eof:  b%0b\n",
            "rdy:  b%0b\n",
            "eeof: b%0b\n",
            "edb:  h%0h\n",
            "link_status:  b%0b\n",
            "err: b%0b\n",
            "crc_ok: b%0b\n",
            "crc_vld: b%0b\n"},
            super.convert2string(),
            data,
            bytes_vld,
            sof,
            eof,
            rdy,
            eeof,
            edb,
            link_status,
            err,
            rxseqerr,
            rxblkerr,
            rxidle,
            rxrmterr,
            rxlocerr,
            crc_ok,
            crc_vld
            );
        return s;
    endfunction: convert2string

endclass

`endif
