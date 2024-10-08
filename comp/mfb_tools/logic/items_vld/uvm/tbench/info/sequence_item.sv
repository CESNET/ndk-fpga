// pkg.sv
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


// Items description
//
// ============ ==================================================================
// CHSUM_EN     Checksum enable.
// LENGTH       Length of chunk from which is calculated chsum.
// OFFSET       Offset of chunk.
// PAYLOAD_SIZE Size of data payload.
// ============ ==================================================================


// This class represents high level transaction, which can be reusable for other components.
class sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) extends uvm_sequence_item;
    // Registration of object tools.
    `uvm_object_param_utils(uvm_header_type::sequence_item#(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------

    rand logic [LENGTH_WIDTH-1 : 0]    length;
    rand logic [OFFSET_WIDTH-1 : 0]    offset;
    rand logic [$clog2(PKT_MTU)-1 : 0] payload_size;
    rand logic                         chsum_en;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -----------------------
    // Common UVM functions.
    // -----------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        chsum_en = rhs_.chsum_en;
        length = rhs_.length;
        offset = rhs_.offset;
        payload_size = rhs_.payload_size;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item #(PKT_MTU, OFFSET_WIDTH, LENGTH_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret  = super.do_compare(rhs, comparer);
        ret &= (chsum_en == rhs_.chsum_en);
        ret &= (length == rhs_.length);
        ret &= (offset == rhs_.offset);
        ret &= (payload_size == rhs_.payload_size);
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string ret;


        ret = $sformatf("\n\tchsum_en : %b\n\tlength : %d\n\toffset : %d\n\tpayload_size : %d\n",
                     chsum_en, length, offset, payload_size);

        return ret;
    endfunction
endclass

