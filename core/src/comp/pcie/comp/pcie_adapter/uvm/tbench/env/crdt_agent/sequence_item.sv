//-- sequence_item.sv: Item for AVST credit control sequencer
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 

class sequence_item extends uvm_sequence_item;

    // ------------------------------------------------------------------------
    // Registration of object tools
    `uvm_object_utils(uvm_crdt::sequence_item)

    // ------------------------------------------------------------------------
    // Bus structure of Credit Control bus
    rand logic init_done;
    rand logic [6-1 : 0] update   ;
    rand logic [2-1 : 0] cnt_ph   ;
    rand logic [2-1 : 0] cnt_nph  ;
    rand logic [2-1 : 0] cnt_cplh ;
    rand logic [4-1 : 0] cnt_pd   ;
    rand logic [4-1 : 0] cnt_npd  ;
    rand logic [4-1 : 0] cnt_cpld ;

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Common UVM functions

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "mvb::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        init_done = rhs_.init_done;
        update    = rhs_.update;
        cnt_ph    = rhs_.cnt_ph;
        cnt_nph   = rhs_.cnt_nph;
        cnt_cplh  = rhs_.cnt_cplh;
        cnt_pd    = rhs_.cnt_pd;
        cnt_npd   = rhs_.cnt_npd;
        cnt_cpld  = rhs_.cnt_cpld;
    endfunction

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compare all attributes that maters
        return (super.do_compare(rhs, comparer) &&
            (init_done === rhs_.init_done)      &&
            (update    === rhs_.update)         &&
            (cnt_ph    === rhs_.cnt_ph)         &&
            (cnt_nph   === rhs_.cnt_nph)        &&
            (cnt_cplh  === rhs_.cnt_cplh)       &&
            (cnt_pd    === rhs_.cnt_pd)         &&
            (cnt_npd   === rhs_.cnt_npd)        &&
            (cnt_cpld  === rhs_.cnt_cpld));

    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string;

        output_string = $sformatf("\n\tINIT_DONE: %b \n\tUPDATE 0x%h \n\tCNT_PH 0x%h \n\tCNT_NPH 0x%h \n\tCNT_CPLH 0x%h \n\tCNT_PD 0x%h \n\tCNT_NPD 0x%h \n\tCNT_CPLD 0x%h \n",
            init_done, update, cnt_ph, cnt_nph, cnt_cplh, cnt_pd, cnt_npd, cnt_cpld
        );

        return output_string;
    endfunction

endclass
