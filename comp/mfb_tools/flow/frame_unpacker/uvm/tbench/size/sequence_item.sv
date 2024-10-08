// pkg.sv
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


// Items description
//
// ========= ==================================================================
// SIZE      Size of SP.
// ========= ==================================================================


// This class represents high level transaction, which can be reusable for other components.
class sequence_item extends uvm_sequence_item;
    // Registration of object tools.
    `uvm_object_utils(uvm_superpacket_size::sequence_item)

    // -----------------------
    // Variables.
    // -----------------------

    rand int sp_size;

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
        sp_size    = rhs_.sp_size;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret  = super.do_compare(rhs, comparer);
        ret &= (sp_size    == rhs_.sp_size);
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string ret;

        ret = $sformatf("\tsp_size : %d\n", sp_size);

        return ret;
    endfunction
endclass

