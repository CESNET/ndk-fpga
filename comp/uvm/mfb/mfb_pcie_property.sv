//-- mfb_pcie_property.sv: Properties for mfb pcie bus
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MFB_PCIE_PROPERTY
`define MFB_PCIE_PROPERTY


`include "uvm_macros.svh"
import uvm_pkg::*;

`include "mfb_property.sv"

module mfb_pcie_property #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned BLOCK_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    logic STRADDLING
)(
    input RESET,
    mfb_if vif
);

    mfb_property #(
        .REGIONS     (REGIONS    ),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE ),
        .ITEM_WIDTH  (ITEM_WIDTH ),
        .META_WIDTH  (META_WIDTH )
    ) MFB_BASE (
        .RESET (RESET),
        .vif   (vif  )
    );

    generate if (STRADDLING  == 1'b1) begin : gen_straddling
        property prop_straddling(int unsigned region);
            @(posedge vif.CLK)
            disable iff(RESET)
            vif.SRC_RDY && vif.SOF[region] |-> vif.EOF[region-1];
        endproperty

        for(genvar it = 1; it < REGIONS; it++) begin : gen_straddling_assert
            assert property (prop_straddling(it))
                else begin
                    `uvm_error($sformatf("%m"),
                        $sformatf(
                            "\n\tWhen straddling is enabled before sof have to be eof.\n\tThis is broken at region %0d",
                                it));
                end
        end
    end else begin : gen_nostraddling
        property prop_nostraddling(int unsigned region);
            @(posedge vif.CLK)
            disable iff(RESET)
            vif.SRC_RDY && (vif.SOF[region] == 0);
        endproperty

        for(genvar it = 1; it < REGIONS; it++) begin : gen_nostraddling_assert
            assert property (prop_nostraddling(it))
                else begin
                    `uvm_error($sformatf("%m"),
                        $sformatf("\n\tWhen straddling is Disabled Then SOP can be only in first region"));
                end
        end
    end endgenerate
endmodule


`endif
