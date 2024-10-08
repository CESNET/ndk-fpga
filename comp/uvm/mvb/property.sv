//-- property.sv: Properties for mvb bus
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`include "uvm_macros.svh"
import uvm_pkg::*;


module mvb_property #(int unsigned ITEMS, int unsigned ITEM_WIDTH)
    (
        input RESET,
        mvb_if vif
    );
    string module_name = "";
    logic START = 1'b1;

    // -----------------------
    // Properties.
    // -----------------------

    // This property check if SRC_RDY does not does low until DST_RDY is low
    property src_rdy_high_until_dst_rdy_high;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        $rose(vif.SRC_RDY) |-> (vif.SRC_RDY until vif.DST_RDY);
    endproperty

    // This property check if at least one VLD is high when SRC_RDY is high
    property src_rdy_high_only_when_at_least_one_vld_high;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        $rose(vif.SRC_RDY) |-> |vif.VLD;
    endproperty


    //////////////////////
    // UNKNOWN PROPERTY
    property src_rdy_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.SRC_RDY);
    endproperty


    property vld_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        vif.SRC_RDY |-> !$isunknown(vif.VLD);
    endproperty

    property item_undefined(int unsigned item);
        @(posedge vif.CLK)
        disable iff(RESET || START)
        (vif.SRC_RDY && vif.VLD[item]) |-> !$isunknown(vif.DATA[(item+1)*ITEM_WIDTH -1 -: ITEM_WIDTH]);
    endproperty

    initial begin
        $sformat(module_name, "%m");
        @(posedge vif.CLK)
        #(10ps)
        START = 1'b0;
    end

    // -----------------------
    // Assertion.
    // -----------------------
    assert property (src_rdy_high_until_dst_rdy_high)
        else begin
            `uvm_error(module_name,  "\n\tMVB interface SRC_RDY drops before DST_RDY was rised.");
        end

    assert property (src_rdy_high_only_when_at_least_one_vld_high)
        else begin
            `uvm_error(module_name, "\n\tMVB interface There is no valid data but SRC_RDY is high.");
        end

    assert property (src_rdy_undefined)
        else begin
            `uvm_error(module_name, "\n\tMVB interface SRC RDY have to allways be valid when RESET is not set");
        end

    assert property (vld_undefined)
        else begin
            `uvm_error(module_name, "\n\tMVB interface when SRC RDY is set then VLD signal have to be valid");
        end

    for(genvar it = 0; it < ITEMS; it++) begin
        assert property (item_undefined(it))
            else begin
                `uvm_error(module_name, $sformatf("\n\tMVB interface when SRC RDY VLD[%0d] is asserted then propper part of DATA[%0d-1 -: %0d] have to be valid", it, (it+1)*ITEM_WIDTH, it*ITEM_WIDTH));
            end
    end

endmodule
