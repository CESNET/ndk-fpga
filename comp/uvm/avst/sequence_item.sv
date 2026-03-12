//-- sequence_item.sv: Item for mfb sequencer
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class sequence_item #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH) extends uvm_common::sequence_item;

    // ------------------------------------------------------------------------
    // Registration of object tools
    `ndk_object_param_utils(
        uvm_avst::sequence_item#(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH),
        $sformatf("uvm_avst::sequence_item#(%0d,%0d,%0d,%0d)",REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH)
    )

    // ------------------------------------------------------------------------
    // Member attributes, equivalent with interface pins
    localparam DATA_WIDTH =  REGION_SIZE * ITEM_WIDTH;
    localparam SOF_POS_WIDTH = $clog2(REGION_SIZE);
    localparam EMPTY_WIDTH = $clog2(REGION_SIZE);

    // ------------------------------------------------------------------------
    // Bus structure of mfb
    rand logic [DATA_WIDTH       -1 : 0] data  [REGIONS];
    rand logic [META_WIDTH       -1 : 0] meta  [REGIONS];
    rand logic [EMPTY_WIDTH      -1 : 0] empty [REGIONS];
    rand logic [REGIONS          -1 : 0] sop;
    rand logic [REGIONS          -1 : 0] eop;
    rand logic [REGIONS          -1 : 0] valid;
    rand logic ready;


    // ------------------------------------------------------------------------
    // Constructor
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // Common UVM functions

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "mvb::sequence_item::do_copy:", "Failed to cast transaction object." )
            return;
        end

        // Now copy all attributes.
        super.do_copy(rhs);
        data  = rhs_.data;
        meta  = rhs_.meta;
        empty = rhs_.empty;
        sop   = rhs_.sop;
        eop   = rhs_.eop;
        valid = rhs_.valid;
        ready = rhs_.ready;
    endfunction

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item #(REGIONS, REGION_SIZE, ITEM_WIDTH, META_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compare all attributes that maters
        return (super.do_compare(rhs, comparer) &&
            (data  == rhs_.data)                &&
            (meta  == rhs_.meta)                &&
            (empty == rhs_.empty)               &&
            (sop   == rhs_.sop)                 &&
            (eop   == rhs_.eop)                 &&
            (valid == rhs_.valid)               &&
            (ready == rhs_.ready));

    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string ret = "";

        ret = $sformatf("\n\tRAEDY: %b\n", ready);

        for (int unsigned it = 0; it < REGIONS; it++) begin
            ret = {ret, $sformatf("\n\tREGION %0d\n\t\tVALID %0d\n\t\tSOP %0d\n\t\tEOP %0d EMTPY %0d\n\t\tMETA 0x%h\n\t\tDATA(HEX)", it, valid[it], sop[it], eop[it], empty[it], meta[it])};
            for (int unsigned jt = 0; jt < REGION_SIZE; jt++) begin
                if (jt % 8 == 0) begin
                    ret = {ret, "\n\t\t"};
                end
                ret = {ret, $sformatf("%h ", data[it][(jt+1)*ITEM_WIDTH-1 -: ITEM_WIDTH])};
            end
        end

        return ret;
    endfunction

endclass
