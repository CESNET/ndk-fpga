/*
 * file       : transaction.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: byte array transaction
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_SEQUENCE_ITEM_SV
`define BYTE_ARRAY_SEQUENCE_ITEM_SV

// This class represents high level transaction, which can be reusable for other components.
class sequence_item extends uvm_common::sequence_item;

    // Registration of object tools.
    `uvm_object_utils(uvm_byte_array::sequence_item)

    // -----------------------
    // Variables.
    // -----------------------

    rand byte unsigned data[]; // Generate random data.

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -----------------------
    // Common UVM functions.
    // -----------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item rhs_;

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
        sequence_item rhs_;

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
        string ret;

        $sformat(ret, "%s\n\tByte_array::sequence_item size %0d", super.convert2string(), data.size());
        for (int unsigned it = 0; it < data.size(); it++) begin
            if (it % 32 == 0) begin
                $sformat(ret, "%s\n\t\t%2h", ret, data[it]);
            end else if (it % 8 == 0) begin
                $sformat(ret, "%s    %2h", ret, data[it]);
            end else begin
                $sformat(ret, "%s %2h", ret, data[it]);
            end
        end
        return ret;
    endfunction

    function int unsigned size();
        return data.size();
    endfunction
endclass

`endif
