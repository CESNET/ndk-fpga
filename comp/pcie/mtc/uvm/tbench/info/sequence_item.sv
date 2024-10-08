//-- pkg.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


// This class represents high level transaction, which can be reusable for other components.
class sequence_item extends uvm_sequence_item;
    // Registration of object tools.
    `uvm_object_utils(uvm_pcie_hdr::sequence_item)

    // -----------------------
    // Variables.
    // -----------------------

    // CQ PCIE HDR
    rand logic [64-1:0] addr;
    rand logic [11-1:0] dw_count;
    rand logic [8-1:0]  req_type;
    rand logic [8-1:0]  intel_type;
    rand logic [16-1:0] req_id;
    rand logic [8-1:0]  tag;
    rand logic [8-1:0]  t_func;
    rand logic [6-1:0]  bar_ap;
    rand logic [3-1:0]  tc;
    rand logic [3-1:0]  attr;
    // Others
    // prefix [160-1 : 128] = '0;
    rand logic [3-1:0]  bar;
    rand logic [4-1:0]  fbe;
    rand logic [4-1:0]  lbe;
    rand logic [1-1:0]  tph_present;
    rand logic [2-1:0]  tph_type;
    rand logic [8-1:0]  tph_st_tag;

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
        addr        = rhs_.addr;
        dw_count    = rhs_.dw_count;
        req_type    = rhs_.req_type;
        intel_type  = rhs_.intel_type;
        req_id      = rhs_.req_id;
        tag         = rhs_.tag;
        t_func      = rhs_.t_func;
        bar_ap      = rhs_.bar_ap;
        tc          = rhs_.tc;
        attr        = rhs_.attr;
        bar         = rhs_.bar;
        fbe         = rhs_.fbe;
        lbe         = rhs_.lbe;
        tph_present = rhs_.tph_present;
        tph_type    = rhs_.tph_type;
        tph_st_tag  = rhs_.tph_st_tag;
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

        ret &= (addr        == rhs_.addr       );
        ret &= (dw_count    == rhs_.dw_count   );
        ret &= (req_type    == rhs_.req_type   );
        ret &= (intel_type  == rhs_.intel_type );
        ret &= (req_id      == rhs_.req_id     );
        ret &= (tag         == rhs_.tag        );
        ret &= (t_func      == rhs_.t_func     );
        ret &= (bar_ap      == rhs_.bar_ap     );
        ret &= (tc          == rhs_.tc         );
        ret &= (attr        == rhs_.attr       );
        ret &= (bar         == rhs_.bar        );
        ret &= (fbe         == rhs_.fbe        );
        ret &= (lbe         == rhs_.lbe        );
        ret &= (tph_present == rhs_.tph_present);
        ret &= (tph_type    == rhs_.tph_type   );
        ret &= (tph_st_tag  == rhs_.tph_st_tag );

        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string ret;

        ret = $sformatf( "\tAddress_type : 0x%h\n\tAddress : 0x%h\n\tDword count : %0d\n\tRequest_type : x%b\n\tIntel_type : 0x%h\n\tRequest_id : %0d\n\tTag : %0d\n\tTarget_function : 0x%h\n\tBar_aperture : %0d\n\tTransaction_class : 0x%h\n\tSnoop bit : 0x%h\n\tRelax bit : 0x%h\n\tID-based : 0x%h\n\tBar : %0d\n\tFBE : x%b\n\tLBE : x%b\n\ttph_present : 0x%h\n\ttph_type : 0x%h\n\ttph_st_tag : 0x%h\n", addr[2-1 : 0], addr[64-1 : 2], dw_count, req_type, intel_type, req_id, tag, t_func, bar_ap, tc, attr[0], attr[1], attr[2], bar, fbe, lbe, tph_present, tph_type, tph_st_tag);

        return ret;
    endfunction
endclass

