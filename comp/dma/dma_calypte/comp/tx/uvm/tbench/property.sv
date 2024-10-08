// property.sv
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

module TX_DMA_CALYPTE_PROPERTY #(
    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,

    int unsigned PCIE_CQ_MFB_REGIONS,
    int unsigned PCIE_CQ_MFB_REGION_SIZE,
    int unsigned PCIE_CQ_MFB_BLOCK_SIZE,
    int unsigned PCIE_CQ_MFB_ITEM_WIDTH,

    int unsigned USR_MFB_META_WIDTH
) (
    input logic RESET,
    mfb_if cq_mfb,
    mfb_if usr_mfb
);

    string module_name = "";
    logic START = 1'b1;

    ///////////////////
    // Start check properties after first clock
    initial begin
        $sformat(module_name, "%m");
        @(posedge usr_mfb.CLK)
        #(10ps)
        START = 1'b0;
    end

    // This property checks that DST_RDY does not drop on the PCIE_CQ interface
    property cq_mfb_dst_rdy_drop;
        @(posedge cq_mfb.CLK)
        disable iff(RESET || START)
        !$fell(cq_mfb.DST_RDY)
    endproperty

    assert property (cq_mfb_dst_rdy_drop)
        else begin
            `uvm_error(module_name, "\n\tCQ_MFB interface: DST_RDY dropped to 0, data loss can occur!");
        end

    mfb_property #(
        .REGIONS     (PCIE_CQ_MFB_REGIONS),
        .REGION_SIZE (PCIE_CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE  (PCIE_CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (PCIE_CQ_MFB_ITEM_WIDTH),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_CQ_META_WIDTH)
    ) cq_mfb_property_i (
        .RESET (RESET),
        .vif   (cq_mfb)
    );

    mfb_property #(
        .REGIONS     (USR_MFB_REGIONS),
        .REGION_SIZE (USR_MFB_REGION_SIZE),
        .BLOCK_SIZE  (USR_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (USR_MFB_ITEM_WIDTH),
        .META_WIDTH  (USR_MFB_META_WIDTH)
    ) usr_mfb_property_i (
        .RESET (RESET),
        .vif   (usr_mfb)
    );
endmodule
