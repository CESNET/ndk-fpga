// property.sv
// Copyright (C) 2022-2024 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

module tx_dma_calypte_property #(
    int unsigned USR_MFB_REGIONS,
    int unsigned USR_MFB_REGION_SIZE,
    int unsigned USR_MFB_BLOCK_SIZE,
    int unsigned USR_MFB_ITEM_WIDTH,

    int unsigned PCIE_CQ_MFB_REGIONS,
    int unsigned PCIE_CQ_MFB_REGION_SIZE,
    int unsigned PCIE_CQ_MFB_BLOCK_SIZE,
    int unsigned PCIE_CQ_MFB_ITEM_WIDTH,

    int unsigned USR_MFB_META_WIDTH,
    int unsigned CHANNELS,
    int unsigned UPD_STOP_REQ_MVB_ITEM_W,
    int unsigned RT_UPD_MVB_ITEM_W
) (
    input logic RESET,
    mfb_if cq_mfb,
    mfb_if usr_mfb,
    mfb_if ptr_upd_mfb,
    mvb_if upd_stop_req_mvb,
    mvb_if chan_start_req_mvb,
    mvb_if rt_upd_mvb
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

    mfb_property #(
        .REGIONS     (PCIE_CQ_MFB_REGIONS),
        .REGION_SIZE (PCIE_CQ_MFB_REGION_SIZE),
        .BLOCK_SIZE  (PCIE_CQ_MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (PCIE_CQ_MFB_ITEM_WIDTH),
        .META_WIDTH  (sv_pcie_meta_pack::PCIE_RQ_META_WIDTH)
    ) ptr_upd_mfb_prop_i (
        .RESET (RESET),
        .vif   (ptr_upd_mfb)
    );

    generate if (PCIE_CQ_MFB_REGIONS > 1) begin : sof_eof_rule_2reg_g
        property ptr_upd_sof_after_eof;
            @(posedge ptr_upd_mfb.CLK) disable iff(RESET)
            ptr_upd_mfb.SRC_RDY |->
                (( ~(ptr_upd_mfb.EOF[PCIE_CQ_MFB_REGIONS-2:0]) & ptr_upd_mfb.SOF[PCIE_CQ_MFB_REGIONS-1:1]) == 0);
        endproperty

        // Check when SOF is not on first position then previous packet have to end in region right before.
        assert property (ptr_upd_sof_after_eof)
            else begin
                `uvm_error(module_name,
                           $sformatf({"\n\tPointer Update interface: If SOF is set on different region ",
                                      "that 0 then the region before has to have EOF set\n\tSOF %b\n\tEOF %b"},
                                     ptr_upd_mfb.SOF, ptr_upd_mfb.EOF));
            end
    end endgenerate

    mvb_property #(
        .ITEMS      (1),
        .ITEM_WIDTH (UPD_STOP_REQ_MVB_ITEM_W)
    ) upd_stop_req_mvb_prop_i (
        .RESET      (RESET),
        .vif        (upd_stop_req_mvb)
    );

    mvb_property #(
        .ITEMS      (1),
        .ITEM_WIDTH ($clog2(CHANNELS))
    ) chan_start_req_mvb_prop_i (
        .RESET      (RESET),
        .vif        (chan_start_req_mvb)
    );

    mvb_property #(
        .ITEMS      (1),
        .ITEM_WIDTH (RT_UPD_MVB_ITEM_W)
    ) rt_upd_mvb_prop_i (
        .RESET      (RESET),
        .vif        (rt_upd_mvb)
    );
endmodule
