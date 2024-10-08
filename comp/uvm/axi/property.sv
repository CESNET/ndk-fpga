//-- property.sv: Properties for AXI bus
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


`include "uvm_macros.svh"
import uvm_pkg::*;


module axi_property
    (
        input RESET,
        axi_if vif
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

    // This property check if TVALID does not does low until DST_RDY is low
    property src_rdy_high_until_dst_rdy_high;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        $rose(vif.TVALID) |-> (vif.TVALID until vif.TREADY);
    endproperty

    //////////////////////
    // TVALID have to be allways valid
    property src_rdy_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.TVALID);
    endproperty

    property dst_rdy_undefined;
        @(posedge vif.CLK)
        disable iff(RESET || START)
        !$isunknown(vif.TREADY);
    endproperty

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

endmodule
