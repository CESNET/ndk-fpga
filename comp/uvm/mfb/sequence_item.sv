//-- sequence_item.sv: Item for mfb sequencer
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_item #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_common::sequence_item;

    // ------------------------------------------------------------------------
    // Registration of object tools
    `uvm_object_param_utils(uvm_mfb::sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH))

    // ------------------------------------------------------------------------
    // Member attributes, equivalent with interface pins
    localparam DATA_WIDTH =  REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
    localparam SOF_POS_WIDTH = $clog2(REGION_SIZE);
    localparam EOF_POS_WIDTH = $clog2(REGION_SIZE * BLOCK_SIZE);

    // ------------------------------------------------------------------------
    // Bus structure of mfb
    rand logic [DATA_WIDTH       -1 : 0] data [REGIONS];
    rand logic [META_WIDTH       -1 : 0] meta [REGIONS];
    rand logic [SOF_POS_WIDTH    -1 : 0] sof_pos [REGIONS];
    rand logic [EOF_POS_WIDTH    -1 : 0] eof_pos [REGIONS];
    rand logic [REGIONS          -1 : 0] sof;
    rand logic [REGIONS          -1 : 0] eof;
    rand logic src_rdy;
    rand logic dst_rdy;


    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Common UVM functions

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "mvb::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        data       = rhs_.data;
        meta        = rhs_.meta;
        sof_pos     = rhs_.sof_pos;
        eof_pos     = rhs_.eof_pos;
        sof         = rhs_.sof;
        eof         = rhs_.eof;
        src_rdy     = rhs_.src_rdy;
        dst_rdy     = rhs_.dst_rdy;
    endfunction

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compare all attributes that maters
        return (super.do_compare(rhs, comparer) &&
            (data      == rhs_.data) &&
            (meta       == rhs_.meta) &&
            (sof_pos    == rhs_.sof_pos) &&
            (eof_pos    == rhs_.eof_pos) &&
            (sof        == rhs_.sof) &&
            (eof        == rhs_.eof) &&
            (src_rdy    == rhs_.src_rdy) &&
            (dst_rdy    == rhs_.dst_rdy));

    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string = "";

        $sformat(output_string, {"\n\tSRC_RDY: %b\n\tDST_RDY: %b\n"},
            src_rdy,
            dst_rdy
        );

        for (int unsigned it = 0; it < REGIONS; it++) begin
            output_string = {output_string, $sformatf("\n\t-- id %0d\n\tEOF %b EOF_POS %0d\n\tSOF %b SOF_POS %0d\n\tDATA %h\n\tMETA %h\n",  it, eof[it], eof_pos[it], sof[it], sof_pos[it], data[it], meta[it])};
        end

        return output_string;
    endfunction

endclass
