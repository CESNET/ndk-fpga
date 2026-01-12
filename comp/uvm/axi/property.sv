//-- property.sv: Properties for AXI bus
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


`include "uvm_macros.svh"
import uvm_pkg::*;


module axi_property #(
        int unsigned ITEMS,
        int unsigned ITEM_WIDTH,
        int unsigned TUSER_WIDTH
    )
    (
        input RESET,
        axi_if vif
    );
    string module_name = "";

    ///////////////////
    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
    end


    // -----------------------
    // Properties.
    // -----------------------

    // This property check if TVALID does not does low until DST_RDY is low
    property src_rdy_high_until_dst_rdy_high;
        @(posedge vif.CLK)
        disable iff(RESET)
        $rose(vif.TVALID) |-> (vif.TVALID until vif.TREADY);
    endproperty

    //////////////////////
    // TVALID have to be allways valid
    property src_rdy_undefined;
        @(posedge vif.CLK)
        disable iff(RESET)
        !$isunknown(vif.TVALID);
    endproperty

    property dst_rdy_undefined;
        @(posedge vif.CLK)
        disable iff(RESET)
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


module axi_xilinx_property #(
        int unsigned ITEMS,
        int unsigned ITEM_WIDTH,
        int unsigned TUSER_WIDTH,
        logic STRADDLING = 1'b0
    )
    (
        input RESET,
        axi_if vif
    );


    axi_property #(
        ITEMS,
        ITEM_WIDTH,
        TUSER_WIDTH
    )
    base (
        .RESET (RESET),
        .vif   (vif)
    );

    //Check straddling
    generate if (STRADDLING  != 1'b0) begin
        //assert property (@(posedge vif.CLK) disable iff(RESET) vif.TLAST === 1'b0)
        //    else begin
        //        `uvm_error($sformatf("%m"), "\n\tIf Straddling is enabled then, last have to be set to zero");
        //    end

        //assert property (@(posedge vif.CLK) disable iff(RESET) vif.TKEEP === '1)
        //    else begin
        //        `uvm_error($sformatf("%m"), "\n\tIf Straddling is enabled then, keep have to be set to all ones");
        //    end

        //property prop_straddling(int unsigned region);
        //    @(posedge axi_cc.CLK)
        //    disable iff(RST)
        //    axi_cc.SRC_RDY && axi_cc.SOF[region] |-> axi_cc.EOF[region-1];
        //endproperty

        //for(genvar it = 1; it < REGIONS; it++) begin
        //    assert property (prop_straddling(it))
        //        else begin
        //            `uvm_error(module_name, $sformatf("\n\tWhen straddling is enabled before sof have to be eof.\n\tThis is broken at region %0d", it));
        //        end
        //end
    end endgenerate
endmodule
