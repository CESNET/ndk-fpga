//-- axi_xilinx_property.sv: Properties for AXI bus (Xilinx)
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef AXI_XILINX_PROPERTY
`define AXI_XILINX_PROPERTY

`include "uvm_macros.svh"
import uvm_pkg::*;

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
        .ITEMS(ITEMS),
        .ITEM_WIDTH(ITEM_WIDTH),
        .TUSER_WIDTH(TUSER_WIDTH)
    )
    base (
        .RESET (RESET),
        .vif   (vif)
    );

    //Check straddling
    generate if (STRADDLING  != 1'b0) begin : gen_straddling
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

`endif
