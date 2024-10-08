/*
 * file       : transaction.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: PMA sequence item
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef PMA_SEQUENCE_ITEM_SV
`define PMA_SEQUENCE_ITEM_SV
// This class represents transaction which contains values of output signals for eth phy
class sequence_item #(int unsigned DATA_WIDTH) extends uvm_common::sequence_item;

    // registration of object tools
    `uvm_object_param_utils(uvm_pma::sequence_item #(DATA_WIDTH))

    // Member attributes, equivalent with interface pins
    // make input attributes random, except for clocks
    rand logic [DATA_WIDTH-1 : 0] data; // Data
    rand logic [2-1 : 0]          hdr; // Header
    rand logic                    data_vld; // Data valid
    rand logic                    hdr_vld; // header valid
    rand logic                    block_lock; // Status of link

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction: new

    // ------------------------
    // Common UVM functions
    // ------------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(DATA_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object." )
            return;
        end
        // Now copy all attributes.
        super.do_copy(rhs);
        data       = rhs_.data;
        hdr        = rhs_.hdr;
        data_vld   = rhs_.data_vld;
        hdr_vld    = rhs_.hdr_vld;
        block_lock = rhs_.block_lock;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(DATA_WIDTH) rhs_;

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
            "data:       h%0h\n",
            "hdr:        d%0d\n",
            "data_vld:   b%0b\n",
            "hdr_vld:    b%0b\n",
            "block_lock: b%0b\n"},
            super.convert2string(),
            data,
            hdr,
            data_vld,
            hdr_vld,
            block_lock
            );
        return s;
    endfunction: convert2string

    constraint c1 {block_lock dist {1'b1 :/ 100, 1'b0 :/ 0};}

endclass

`endif
