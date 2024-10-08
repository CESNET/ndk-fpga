//-- sequence_item.sv: Item for mvb sequencer
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_SEQUENCE_ITEM_SV
`define MVB_SEQUENCE_ITEM_SV

class sequence_item #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_common::sequence_item;

    // ------------------------------------------------------------------------
    // Registration of object tools
    `uvm_object_param_utils(uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH))

    // ------------------------------------------------------------------------
    // Member attributes, equivalent with interface pins
    rand logic [ITEM_WIDTH-1 : 0] data [ITEMS];
    rand logic [ITEMS-1 : 0] vld;
    rand logic src_rdy;
    rand logic dst_rdy;

    constraint data_gen_cons { |vld == 0 -> src_rdy == 0;}

    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Common UVM functions

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(ITEMS, ITEM_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "mvb::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        data        = rhs_.data;
        vld         = rhs_.vld;
        src_rdy     = rhs_.src_rdy;
        dst_rdy     = rhs_.dst_rdy;
    endfunction

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(ITEMS, ITEM_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compare all attributes that maters
        return (super.do_compare(rhs, comparer) &&
            (data       == rhs_.data) &&
            (vld        == rhs_.vld)) &&
            (src_rdy    == rhs_.src_rdy) &&
            (dst_rdy    == rhs_.dst_rdy);
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string = "";
        string data = "";

        $sformat(output_string, {"%s\n\tSRC_RDY: %b\n\tDST_RDY: %b\n"},
            super.convert2string(),
            src_rdy,
            dst_rdy
        );

        // Add new line for each item with correspondence valid bit
        for (int i = 0 ; i < ITEMS ; i++) begin
            $sformat(data, {"\tDATA: 'h%0h\tVLD: %b\n"},
            this.data[i],
            this.vld[i]
            );
            output_string = {output_string, data};
        end

        return output_string;
    endfunction

endclass

`endif
