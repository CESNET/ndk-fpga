//-- property.sv: Properties for mfb bus
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_PROPERTY
`define MFB_PROPERTY


`include "uvm_macros.svh"
import uvm_pkg::*;


module mfb_property #(int unsigned REGIONS, int unsigned REGION_SIZE, int unsigned BLOCK_SIZE, int unsigned ITEM_WIDTH, int unsigned META_WIDTH)
    (
        input RESET,
        mfb_if vif
    );
    string module_name = "";
    logic START = 1'b1;

    ///////////////////
    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
        @(posedge vif.CLK)
        #(10ps)
        START = 1'b0;
    end


    // -----------------------
    // Properties.
    // -----------------------

    // This property check if SRC_RDY does not does low until DST_RDY is low
    property src_rdy_high_until_dst_rdy_high;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        $rose(vif.SRC_RDY) |-> (vif.SRC_RDY until vif.DST_RDY);
    endproperty

    //////////////////////
    // SRC_RDY have to be allways valid
    property src_rdy_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.SRC_RDY);
    endproperty

    property dst_rdy_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.DST_RDY);
    endproperty

    //////////////////////
    // SOF
    property sof_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        vif.SRC_RDY |-> !$isunknown(vif.SOF);
    endproperty

    generate if (REGION_SIZE > 1) begin
        property sof_pos_undefined (int unsigned region);
            @(posedge vif.CLK)
            disable iff(RESET || START)
            (vif.SRC_RDY && vif.SOF[region]) |-> !$isunknown(vif.SOF_POS[(region+1)*$clog2(REGION_SIZE) -1 -: $clog2(REGION_SIZE)]);
        endproperty

        for(genvar it = 0; it < REGIONS; it++) begin
            assert property (sof_pos_undefined(it))
                else begin
                    string num_it;
                    string hi_index;
                    num_it.itoa(it);
                    hi_index.itoa((it+1)*$clog2(REGION_SIZE));
                    `uvm_error(module_name, {"\n\tMFB interface: if SRC_RDY and SOF[", num_it, "] is asserted then coresponding part of SOF_POS [", hi_index ,"-1 -: $clog2(REGION_SIZE)] have to be valid" });
                end
        end
    end endgenerate


    //////////////////////
    // EOF
    property eof_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        vif.SRC_RDY |-> !$isunknown(vif.EOF);
    endproperty


    generate if (REGION_SIZE * BLOCK_SIZE > 1) begin
        property eof_pos_undefined (int unsigned region);
            @(posedge vif.CLK)
            disable iff(RESET || START)
            (vif.SRC_RDY && vif.EOF[region]) |-> !$isunknown(vif.EOF_POS[(region+1)*$clog2(REGION_SIZE * BLOCK_SIZE) -1 -: $clog2(REGION_SIZE * BLOCK_SIZE)]);
        endproperty

        for(genvar it = 0; it < REGIONS; it++) begin
            assert property (eof_pos_undefined(it))
                else begin
                    string num_it;
                    string hi_index;
                    num_it.itoa(it);
                    hi_index.itoa((it+1)*$clog2(REGION_SIZE * BLOCK_SIZE));
                    `uvm_error(module_name, {"\n\tMFB interface: if SRC_RDY and EOF[", num_it, "] is asserted then coresponding part of EOF_POS [", hi_index ,"-1 -: $clog2(REGION_SIZE)] have to be valid" });
                end
        end
    end endgenerate

    // -----------------------
    // Assertion.
    // -----------------------
    assert property (dst_rdy_undefined)
        else begin
            `uvm_error(module_name, "\n\tMFB interface: DST_RDY have to be allways valid if RESET is not set");
        end

    assert property (src_rdy_undefined)
        else begin
            `uvm_error(module_name, "\n\tMFB interface: SRC_RDY have to be allways valid if RESET is not set");
        end

    assert property (src_rdy_high_until_dst_rdy_high)
        else begin
            `uvm_error(module_name, "\n\tMFB interface: SRC_RDY drops before DST_RDY was rised.");
        end

    // SOF EOF assertion
    assert property (sof_undefined)
        else begin
            `uvm_error(module_name, "\n\tMFB interface: if SRC_RDY is asserted then SOF signals have to be valid");
        end

    assert property (eof_undefined)
        else begin
            `uvm_error(module_name, "\n\tMFB interface: if SRC_RDY is asserted then EOF signals have to be valid");
        end

endmodule

`endif

