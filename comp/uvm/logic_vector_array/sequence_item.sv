/*
 * file       : transaction.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte array transaction
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef LOGIC_VECTOR_ARRAY_SEQUENCE_ITEM_SV
`define LOGIC_VECTOR_ARRAY_SEQUENCE_ITEM_SV

// This class represents high level transaction, which can be reusable for other components.
class sequence_item #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_item;

    // Registration of object tools.
    `uvm_object_utils(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------

    rand logic[ITEM_WIDTH-1 : 0] data[]; // Generate random data.

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -----------------------
    // Common UVM functions.
    // -----------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(ITEM_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        data = rhs_.data;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(ITEM_WIDTH) rhs_;

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
        return convert2block(4, 8);
    endfunction

    function string convert2block(int unsigned regions, int unsigned region_width);
        string ret;

        $sformat(ret, "%s\n\tByte_array::sequence_item size %0d", super.convert2string(), data.size());
        for (int unsigned it = 0; it < data.size(); it++) begin
            if (it % (regions*region_width) == 0) begin
                $sformat(ret, "%s\n\t\t%x", ret, data[it]);
            end else if (it % region_width == 0) begin
                $sformat(ret, "%s    %x", ret, data[it]);
            end else begin
                $sformat(ret, "%s %x", ret, data[it]);
            end
        end
        return ret;
    endfunction

    function int unsigned size();
        return data.size();
    endfunction
endclass

`endif
