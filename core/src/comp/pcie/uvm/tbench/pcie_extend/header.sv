// header.sv: This extends pcie header with bar and virtual function.
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:  Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class request_header extends uvm_pcie::request_header;
    // Registration of object tools.
    `uvm_object_utils(uvm_pcie_extend::request_header)

    int unsigned bar;
    int unsigned bar_aperture;
    int unsigned vf;

    function new(string name = "sequence_item");
        super.new(name);
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
        bar          = rhs_.bar;
        bar_aperture = rhs_.bar_aperture;
        vf           = rhs_.vf;
    endfunction: do_copy



    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret = 1;
        request_header rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret = super.do_compare(rhs, comparer);
        ret &= bar           === rhs_.bar;
        ret &= bar_aperture  === rhs_.bar_aperture;
        ret &= vf            === rhs_.vf;
        // Using simple equivalence operator (faster).
        return ret;
    endfunction: do_compare

    function string convert2string();
        string msg = super.convert2string();
        msg = {msg, $sformatf("\tbar : %0d bar aperture : %0d\n\tvf : %0d\n", bar, bar_aperture, vf)};
        return msg;
    endfunction
endclass



