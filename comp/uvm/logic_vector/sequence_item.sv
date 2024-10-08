//-- sequence_item.sv: logic vector sequence item(transaction)
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

// This class represents high level transaction, which can be reusable for other components.
class sequence_item #(int unsigned DATA_WIDTH)extends uvm_common::sequence_item;

    // Registration of object tools.
    `uvm_object_param_utils(uvm_logic_vector::sequence_item#(DATA_WIDTH))

    // -----------------------
    // Variables.
    // -----------------------
    rand logic [DATA_WIDTH-1:0] data; // Generate random data.

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction: new

    // -----------------------
    // Common UVM functions.
    // -----------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(DATA_WIDTH) rhs_;

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
        sequence_item #(DATA_WIDTH) rhs_;
        bit ret;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("logic_vector::sequence_item#(DATA_WIDTH)::do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= (rhs_.data === data);

        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string s;
        $sformat(s, {
            "%s\n",
            "data         = h%0h"},
            super.convert2string(), data);
        return s;
    endfunction

endclass
