//-- property.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

module MTC_PROPERTY  #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH)
    (
        input logic RESET,
        mfb_if   mfb_cq,
        mfb_if   mfb_cc,
        mi_if    config_mi
    );

    string module_name = "";
    logic START = 1'b1;

    ///////////////////
    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
        @(posedge mfb_cc.CLK)
        #(10ps)
        START = 1'b0;
    end

    ////////////////////////////////////
    // RX PROPERTY
    mfb_property #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE ),
        .ITEM_WIDTH  (ITEM_WIDTH ),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
    )
    MFB_CQ (
        .RESET (RESET),
        .vif   (mfb_cq)
    );


    ////////////////////////////////////
    // TX PROPERTY
    mfb_property #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_CC_META_WIDTH)
    )
    MFB_CC (
        .RESET (RESET),
        .vif   (mfb_cc)
    );

    //simplyfied rule
    property sof_eof_src_rdy;
        @(posedge mfb_cc.CLK) disable iff(RESET || START)
        (mfb_cc.SRC_RDY && (mfb_cc.SOF != 0)) |-> mfb_cc.SRC_RDY s_until_with (mfb_cc.EOF != 0);
    endproperty

    assert property (sof_eof_src_rdy)
        else begin
            `uvm_error(module_name, "\n\tMFB To PCIE must'n stop sending data in middle of frame");
        end


endmodule
