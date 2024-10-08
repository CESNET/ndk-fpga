//-- sequence_item.sv: Item for AXI sequencer
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_item #(int unsigned DATA_WIDTH, int unsigned TUSER_WIDTH, int unsigned REGIONS) extends uvm_common::sequence_item;

    // ------------------------------------------------------------------------
    // Registration of object tools
    `uvm_object_param_utils(uvm_axi::sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS))

    // ------------------------------------------------------------------------
    // Member attributes, equivalent with interface pins
    localparam ITEM_WIDTH = 32;
    localparam TKEEP_WIDTH = DATA_WIDTH/ITEM_WIDTH;

    // ------------------------------------------------------------------------
    // Bus structure of mfb
    rand logic [DATA_WIDTH/REGIONS  -1 : 0] tdata [REGIONS];
    rand logic [TUSER_WIDTH -1 : 0] tuser;
    rand logic [TKEEP_WIDTH -1 : 0] tkeep;
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
        sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS) rhs_;

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
        sequence_item #(DATA_WIDTH, TUSER_WIDTH, REGIONS) rhs_;

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
        string output_string = "";

        output_string = $sformatf({"\n\tTDATA: %b\n\tTUSER: %b\n\tTKEEP: %b\n\tTLAST: %b\n\tTVALID: %b\n\tTREADY: %b\n"},
            tdata,
            tuser,
            tkeep,
            tlast,
            tvalid,
            tready
        );

        for (int unsigned it = 0; it < REGIONS; it++) begin
            output_string = {output_string, $sformatf("\n\t-- id %0d\n\tDATA %h\n",  it, tdata[it])};
        end

        return output_string;
    endfunction

endclass
