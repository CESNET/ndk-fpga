//-- avst_pcie_propert.sv: Properties for avst pcie bus
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef AVST_PCIE_PROPERT
`define AVST_PCIE_PROPERT


`include "uvm_macros.svh"
import uvm_pkg::*;

`include "avst_property.sv"

module avst_pcie_propert #(
    int unsigned REGIONS,
    int unsigned REGION_SIZE,
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    logic STRADDLING
)(
    input RESET,
    mfb_if vif
);

    avst_property #(
        .REGIONS     (REGIONS    ),
        .REGION_SIZE (REGION_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH ),
        .META_WIDTH  (META_WIDTH )
    ) AVST_BASE (
        .RESET (RESET),
        .vif   (vif  )
    );

    generate if (STRADDLING  == 1'b1) begin : gen_straddling
        property prop_straddling(int unsigned region);
            @(posedge vif.CLK)
            disable iff(RESET)
            vif.SRC_RDY && vif.SOP[region] |-> vif.EOP[region-1];
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
            vif.SRC_RDY && (vif.SOP[region] == 0);
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
