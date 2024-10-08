//-- property.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

module DMA_LL_PROPERTY  #(DEVICE, USER_REGIONS, USER_REGION_SIZE, USER_BLOCK_SIZE, USER_ITEM_WIDTH, PCIE_UP_REGIONS, PCIE_UP_REGION_SIZE, PCIE_UP_BLOCK_SIZE, PCIE_UP_ITEM_WIDTH, CHANNELS, PKT_SIZE_MAX)
    (
        input logic RESET,
        mfb_if   mfb_rx,
        mfb_if   mfb_tx,
        mi_if    config_mi
    );

    localparam USER_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);


    string module_name = "";
    logic START = 1'b1;

    ///////////////////
    // Start check properties after first clock
    initial begin
        module_name = $sformatf("%m");
        @(posedge mfb_tx.CLK)
        #(10ps)
        START = 1'b0;
    end

    ////////////////////////////////////
    // RX PROPERTY
    mfb_property #(
        .REGIONS     (USER_REGIONS),
        .REGION_SIZE (USER_REGION_SIZE),
        .BLOCK_SIZE  (USER_BLOCK_SIZE ),
        .ITEM_WIDTH  (USER_ITEM_WIDTH ),
        .META_WIDTH  (USER_META_WIDTH)
    )
    MFB_RX (
        .RESET (RESET),
        .vif   (mfb_rx)
    );


    ////////////////////////////////////
    // TX PROPERTY
    mfb_property #(
        .REGIONS     (PCIE_UP_REGIONS),
        .REGION_SIZE (PCIE_UP_REGION_SIZE),
        .BLOCK_SIZE  (PCIE_UP_BLOCK_SIZE),
        .ITEM_WIDTH  (PCIE_UP_ITEM_WIDTH),
        .META_WIDTH  (0)
    )
    MFB_TX (
        .RESET (RESET),
        .vif   (mfb_tx)
    );

    //simplyfied rule
    property sof_eof_src_rdy;
        @(posedge mfb_tx.CLK) disable iff(RESET || START)
        (mfb_tx.SRC_RDY && (mfb_tx.SOF != 0)) |-> mfb_tx.SRC_RDY s_until_with (mfb_tx.EOF != 0);
    endproperty

    assert property (sof_eof_src_rdy)
        else begin
            `uvm_error(module_name, "\n\tMFB To PCIE must'n stop sending data in middle of frame");
        end
endmodule
