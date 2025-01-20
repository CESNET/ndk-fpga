//-- properties.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:  Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"


module PROPERTY #(
    string ENDPOINT_TYPE,

    int unsigned RC_MFB_REGIONS,
    int unsigned RC_MFB_REGION_SIZE,
    int unsigned RC_MFB_BLOCK_SIZE,
    int unsigned RC_MFB_ITEM_WIDTH,
    int unsigned RC_MFB_META_W,

    int unsigned CQ_MFB_REGIONS,
    int unsigned CQ_MFB_REGION_SIZE,
    int unsigned CQ_MFB_BLOCK_SIZE,
    int unsigned CQ_MFB_ITEM_WIDTH,
    int unsigned CQ_MFB_META_W

)
(
    input logic RST,
    // For Intel
    avst_if avst_down,
    avst_if avst_up,
    // Credit control
    crdt_if crdt_down,
    crdt_if crdt_up,
    // For Xilinx
    axi_if cq_axi,
    axi_if cc_axi,
    axi_if rc_axi,
    axi_if rq_axi,
    // For Intel and Xilinx
    mfb_if rq_mfb,
    mfb_if rc_mfb,
    mfb_if cq_mfb,
    mfb_if cc_mfb
);

    string module_name = "";
    logic START = 1'b1;

    ///////////////////
    // Start check properties after first clock
    initial begin
        module_name = $sformatf("%m");
        #(10ps)
        START = 1'b0;
    end

    ////////////////////////////////////
    // RC
    mfb_property #(
        .REGIONS     (RC_MFB_REGIONS    ),
        .REGION_SIZE (RC_MFB_REGION_SIZE),
        .BLOCK_SIZE  (RC_MFB_BLOCK_SIZE ),
        .ITEM_WIDTH  (RC_MFB_ITEM_WIDTH ),
        .META_WIDTH  (RC_MFB_META_W     )
    )
    RC (
        .RESET (RST),
        .vif   (rc_mfb)
    );

    ////////////////////////////////////
    // CQ
    mfb_property #(
        .REGIONS     (CQ_MFB_REGIONS    ),
        .REGION_SIZE (CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE  (CQ_MFB_BLOCK_SIZE ),
        .ITEM_WIDTH  (CQ_MFB_ITEM_WIDTH ),
        .META_WIDTH  (CQ_MFB_META_W     )
    )
    CQ (
        .RESET (RST),
        .vif   (cq_mfb)
    );

    generate if (ENDPOINT_TYPE == "R_TILE") begin
        property no_fall_init;
            @(posedge avst_down.CLK) disable iff(RST || START)
            $rose(avst_down.READY) |=> always avst_down.READY;
        endproperty

        assert property (no_fall_init)
            else begin
                `uvm_error(module_name, "\n\tAVST DOWN interface broke protocol R_TILE. The READY signal falls down after inintialization");
            end
    end endgenerate
endmodule

