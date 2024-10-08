/*
 * file       : testbench
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: testbench
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`include "uvm_macros.svh"
import uvm_pkg::*;


module testbench;


    logic CLK = 0;
    intel_mac_seg_if #(test::SEGMENTS) tx_mac_seg(CLK);
    mfb_if #(test::REGIONS, test::REGION_SIZE, 8, 8, 1) rx_mac_seg(CLK);
    reset_if                           reset(CLK);

    always #(test::CLK_PERIOD/2) CLK = ~CLK;

    TX_MAC_LITE_ADAPTER_MAC_SEG  #(
        .REGIONS      (test::REGIONS),
        .REGION_SIZE  (test::REGION_SIZE),
        .SEGMENTS     (test::SEGMENTS)
    )
    DUT_U (
        .CLK              (CLK),
        .RESET            (reset.RESET),
        // INPUT
        .IN_MFB_DATA      (rx_mac_seg.DATA),
        .IN_MFB_SOF       (rx_mac_seg.SOF),
        .IN_MFB_SOF_POS   (rx_mac_seg.SOF_POS),
        .IN_MFB_EOF       (rx_mac_seg.EOF),
        .IN_MFB_EOF_POS   (rx_mac_seg.EOF_POS),
        .IN_MFB_ERROR     (rx_mac_seg.META),
        .IN_MFB_SRC_RDY   (rx_mac_seg.SRC_RDY),
        .IN_MFB_DST_RDY   (rx_mac_seg.DST_RDY),

        // OUTPUT
        .OUT_MAC_DATA      (tx_mac_seg.DATA),
        .OUT_MAC_INFRAME   (tx_mac_seg.INFRAME),
        .OUT_MAC_EOP_EMPTY (tx_mac_seg.EOP_EMPTY),
        .OUT_MAC_ERROR     (tx_mac_seg.FCS_ERROR),
        .OUT_MAC_VALID     (tx_mac_seg.VALID),
        .OUT_MAC_READY     (tx_mac_seg.READY)
    );


    mac_tx_property #(
        .REGIONS      (test::REGIONS),
        .REGION_SIZE  (test::REGION_SIZE),
        .BLOCK_SIZE   (8),
        .ITEM_WIDTH   (8),
        .META_WIDTH   (1)
    )
    PROPERTY_CHECK (
        .RESET (reset.RESET),
        .mfb_vif (rx_mac_seg)
    );


    initial begin
        uvm_root m_root;

        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_IF", reset);
        uvm_config_db#(virtual intel_mac_seg_if #(test::SEGMENTS))::set(null, "", "TX_MAC_SEQ_IF", tx_mac_seg);
        uvm_config_db#(virtual mfb_if #(test::REGIONS, test::REGION_SIZE, 8, 8, 1))::set(null, "", "RX_MAC_SEQ_IF", rx_mac_seg);

        m_root = uvm_root::get();
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);
        m_root.finish_on_completion = 0;

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

endmodule
