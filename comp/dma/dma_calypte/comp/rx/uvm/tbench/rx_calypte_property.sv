//-- property.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import uvm_pkg::*;
`include "uvm_macros.svh"

module rx_calypte_property #(DEVICE, USR_MFB_REGIONS, USR_MFB_REGION_SIZE, USR_MFB_BLOCK_SIZE, USR_MFB_ITEM_WIDTH,
                          PCIE_RQ_REGIONS, PCIE_RQ_REGION_SIZE, PCIE_RQ_BLOCK_SIZE, PCIE_RQ_ITEM_WIDTH, CHANNELS,
                          PKT_SIZE_MAX)
    (
        input logic RESET,
        mfb_if      usr_mfb,
        mfb_if      pcie_rq_mfb,
        mfb_if      ptr_upd_mfb,
        mi_if       config_mi
    );

    localparam USR_MFB_META_WIDTH = 24 + $clog2(PKT_SIZE_MAX+1) + $clog2(CHANNELS);
    // On Intel devices, every transaction starts in the first region.
    localparam bit IS_INTEL_DEV = (DEVICE == "STRATIX10" || DEVICE == "AGILEX");


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

    mfb_property #(
        .REGIONS     (PCIE_RQ_REGIONS),
        .REGION_SIZE (PCIE_RQ_REGION_SIZE),
        .BLOCK_SIZE  (PCIE_RQ_BLOCK_SIZE),
        .ITEM_WIDTH  (PCIE_RQ_ITEM_WIDTH),
        .META_WIDTH  (0)
    )
    ptr_upd_mfb_property_i (
        .RESET (RESET),
        .vif   (ptr_upd_mfb)
    );

    pcie_rq_mfb_property #(
        .REGIONS               (PCIE_RQ_REGIONS),
        .SOF_FIRST_REGION_ONLY (IS_INTEL_DEV),
        .IF_NAME               ("Data interface")
    ) pcie_rq_mfb_frame_property_i (
        .RESET (RESET),
        .vif   (pcie_rq_mfb)
    );

    pcie_rq_mfb_property #(
        .REGIONS               (PCIE_RQ_REGIONS),
        .SOF_FIRST_REGION_ONLY (IS_INTEL_DEV),
        .IF_NAME               ("Pointer Update interface")
    ) ptr_upd_mfb_frame_property_i (
        .RESET (RESET),
        .vif   (ptr_upd_mfb)
    );
endmodule
