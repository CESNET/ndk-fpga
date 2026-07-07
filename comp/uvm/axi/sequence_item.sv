//-- sequence_item.sv: Item for AXI sequencer
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_item #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned TUSER_WIDTH
) extends uvm_common::sequence_item;

    // ------------------------------------------------------------------------
    // Registration of object tools
    `ndk_object_param_utils(
        uvm_axi::sequence_item#(ITEMS, ITEM_WIDTH, TUSER_WIDTH),
        $sformatf("uvm_axi::sequence_item#(%0d,%0d,%0d)",ITEMS, ITEM_WIDTH, TUSER_WIDTH)
    )

    // ------------------------------------------------------------------------
    // Bus structure of mfb
    rand logic [ITEMS*ITEM_WIDTH -1 : 0] tdata;
    rand logic [TUSER_WIDTH -1 : 0] tuser;
    rand logic [ITEMS -1 : 0]       tkeep;
    rand logic                      tlast;
    rand logic                      tvalid;
    rand logic                      tready;


    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Common UVM functions

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "axi::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        tdata  = rhs_.tdata;
        tuser  = rhs_.tuser;
        tkeep  = rhs_.tkeep;
        tlast  = rhs_.tlast;
        tvalid = rhs_.tvalid;
        tready = rhs_.tready;
    endfunction

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(ITEMS, ITEM_WIDTH, TUSER_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compare all attributes that maters
        return (super.do_compare(rhs, comparer) &&
            (tdata  == rhs_.tdata) &&
            (tuser  == rhs_.tuser) &&
            (tkeep  == rhs_.tkeep) &&
            (tlast  == rhs_.tlast) &&
            (tvalid == rhs_.tvalid) &&
            (tready == rhs_.tready));

    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string ret = "";

        ret = {ret, "\n\tTDATA :"};
        for (int unsigned it = 0; it < ITEMS; it++) begin
            if (it % 8 == 0) begin
                ret = {ret, "\n\t"};
            end

            ret = {ret, $sformatf("'h%0h  ", tdata[(it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH])};
        end


        ret = {ret, $sformatf({"\n\tTUSER: 'h%h\n\tTKEEP: 'b%b\n\tTLAST: 'b%b\n\tTVALID: 'b%b\n\tTREADY: 'b%b\n"},
            tuser,
            tkeep,
            tlast,
            tvalid,
            tready
        )};

        return ret;
    endfunction

endclass
