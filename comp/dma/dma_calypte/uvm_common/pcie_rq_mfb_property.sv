// pcie_rq_mfb_property.sv: Checks of the frame layout on a PCIe RQ MFB interface of DMA Calypte
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef DMA_CALYPTE_PCIE_RQ_MFB_PROPERTY
`define DMA_CALYPTE_PCIE_RQ_MFB_PROPERTY

import uvm_pkg::*;
`include "uvm_macros.svh"

// The PCIe hard IP accepts a transaction only when its words are sent in consecutive clock cycles
// and when no region before its start is empty.
module pcie_rq_mfb_property #(
    int unsigned REGIONS,
    // Allow the start of a frame only in the first region. The R-Tile in the single-width mode
    // accepts the start of only one transaction per clock cycle on its TX side.
    bit          SOF_FIRST_REGION_ONLY,
    string       IF_NAME
) (
    input logic RESET,
    mfb_if      vif
);

    string module_name = "";

    // Set when a frame is open after the last transferred word.
    logic               frame_open_reg;
    // Bit r+1 is set when a frame is open after region r of the current word.
    logic [REGIONS:0]   frame_open;

    initial begin
        $sformat(module_name, "%m");
    end

    always_comb begin
        frame_open[0] = frame_open_reg;
        for (int unsigned r = 0; r < REGIONS; r++) begin
            frame_open[r+1] = ( vif.SOF[r] && !vif.EOF[r] && !frame_open[r]) ||
                              ( vif.SOF[r] &&  vif.EOF[r] &&  frame_open[r]) ||
                              (!vif.SOF[r] && !vif.EOF[r] &&  frame_open[r]);
        end
    end

    always_ff @(posedge vif.CLK) begin
        if (RESET) begin
            frame_open_reg <= 1'b0;
        end else if (vif.SRC_RDY && vif.DST_RDY) begin
            frame_open_reg <= frame_open[REGIONS];
        end
    end

    property no_gap_in_frame;
        @(posedge vif.CLK) disable iff (RESET)
        frame_open_reg |-> vif.SRC_RDY;
    endproperty

    assert property (no_gap_in_frame)
        else begin
            `uvm_error(module_name, $sformatf("\n\t%s: SRC_RDY is low in the middle of a frame.", IF_NAME));
        end

    generate if (REGIONS > 1) begin : sof_pos_g
        // A frame can start in region r only when the previous frame ends in region r-1. This also
        // covers an empty region before the start of a frame.
        property sof_after_eof;
            @(posedge vif.CLK) disable iff (RESET)
            vif.SRC_RDY |-> ((~vif.EOF[REGIONS-2:0] & vif.SOF[REGIONS-1:1]) == 0);
        endproperty

        assert property (sof_after_eof)
            else begin
                `uvm_error(module_name, $sformatf({"\n\t%s: SOF is set in a region whose previous region ",
                                                  "does not have EOF set.\n\tSOF 0b%b\n\tEOF 0b%b"},
                                                 IF_NAME, vif.SOF, vif.EOF));
            end
    end endgenerate

    generate if (REGIONS > 1 && SOF_FIRST_REGION_ONLY) begin : sof_first_rgn_g
        property sof_first_region;
            @(posedge vif.CLK) disable iff (RESET)
            vif.SRC_RDY |-> (vif.SOF[REGIONS-1:1] == 0);
        endproperty

        assert property (sof_first_region)
            else begin
                `uvm_error(module_name, $sformatf({"\n\t%s: SOF is set in a region other than the first one.",
                                                  "\n\tSOF 0b%b"}, IF_NAME, vif.SOF));
            end
    end endgenerate

endmodule

`endif
