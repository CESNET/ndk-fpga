/*
 * file       : sequence_item.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: General MII sequence item
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef MII_SEQUENCE_ITEM_SV
`define MII_SEQUENCE_ITEM_SV

class sequence_item #(int unsigned CHANNELS, int unsigned WIDTH) extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_mii::sequence_item #(CHANNELS, WIDTH))

    localparam BYTES = WIDTH >> 3;

    //  Group: Variables
    rand logic [WIDTH - 1 : 0] data [CHANNELS];
    rand logic [BYTES - 1 : 0] control [CHANNELS];
    rand logic clk_en;

    //  Group: Functions

    //  Constructor: new
    function new(string name = "sequence_item");
        super.new(name);
        WHOLE_BYTES : assert((WIDTH & 7) == 0);
    endfunction: new

    //  Function: do_copy
    function void do_copy(uvm_object rhs);
        sequence_item #(CHANNELS, WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "uvm_mii::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        this.data        = rhs_.data;
        this.control     = rhs_.control;
        this.clk_en      = rhs_.clk_en;
    endfunction

    //  Function: do_compare
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(CHANNELS, WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("uvm_mii:do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compare all attributes that maters
        return (super.do_compare(rhs, comparer) &&
            (this.data       == rhs_.data) &&
            (this.control    == rhs_.control) &&
            (this.clk_en     == rhs_.clk_en));
    endfunction

    //  Function: convert2string
    function string convert2string();
        string output_string = "";
        string data = "";

        $sformat(output_string, {"%s\n\tDATA: %b\n\tCONTROL: %b\n\t CLK_EN: %b\n"},
            super.convert2string(),
            this.data,
            this.control,
            this.clk_en
        );

        return output_string;
    endfunction

endclass: sequence_item

`endif
