//-- property.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

module DMA_LL_PROPERTY  #(DEVICE, USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH, PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)
    (
        input logic RESET,
        mfb_if   usr_mfb,
        mfb_if   pcie_rq_mfb,
        mi_if    config_mi
    );

    localparam USR_MFB_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);


    string module_name = "";

    ///////////////////
    // Start check properties after first clock
    initial begin
        module_name = $sformatf("%m");
    end

    ////////////////////////////////////
    // RX PROPERTY
    mfb_property #(
        .REGIONS     (USR_MFB_REGIONS),
        .REGION_SIZE (USR_MFB_REGION_SIZE),
        .BLOCK_SIZE  (USR_MFB_BLOCK_SIZE ),
        .ITEM_WIDTH  (USR_MFB_ITEM_WIDTH ),
        .META_WIDTH  (USR_MFB_META_WIDTH)
    )
    usr_mfb_property_i (
        .RESET (RESET),
        .vif   (usr_mfb)
    );


    ////////////////////////////////////
    // TX PROPERTY
    mfb_property #(
        .REGIONS     (PCIE_RQ_REGIONS),
        .REGION_SIZE (PCIE_RQ_REGION_SIZE),
        .BLOCK_SIZE  (PCIE_RQ_BLOCK_SIZE),
        .ITEM_WIDTH  (PCIE_RQ_ITEM_WIDTH),
        .META_WIDTH  (0)
    )
    pcie_rq_mfb_property_i (
        .RESET (RESET),
        .vif   (pcie_rq_mfb)
    );

    generate if (PCIE_RQ_REGIONS > 1) begin
        property sof_after_eof;
            @(posedge pcie_rq_mfb.CLK) disable iff(RESET)
            pcie_rq_mfb.SRC_RDY |-> (( ~(pcie_rq_mfb.EOF[PCIE_RQ_REGIONS-2:0]) & pcie_rq_mfb.SOF[PCIE_RQ_REGIONS-1:1]) == 0);
        endproperty

        // Check when SOF is not on first position then previous packet have to end in region right before.
        assert property (sof_after_eof)
            else begin
                `uvm_error(module_name, $sformatf("\n\tIf sof is set on different region that 0 then region befor have to be eof set\n\tSOF %b\n\tEOF %b", pcie_rq_mfb.SOF, pcie_rq_mfb.EOF));
            end
    end endgenerate

    //simplyfied rule. No space in middle of packet
    property sof_eof_src_rdy;
        @(posedge pcie_rq_mfb.CLK) disable iff(RESET)
        (pcie_rq_mfb.SRC_RDY && (pcie_rq_mfb.SOF != 0)) |-> pcie_rq_mfb.SRC_RDY s_until_with (pcie_rq_mfb.EOF != 0);
    endproperty

    assert property (sof_eof_src_rdy)
        else begin
            `uvm_error(module_name, "\n\tMFB To PCIE must'n stop sending data in middle of frame");
        end
endmodule
