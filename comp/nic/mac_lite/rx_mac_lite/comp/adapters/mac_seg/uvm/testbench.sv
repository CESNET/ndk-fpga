/*
 * file       : testbench
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: testbench
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`include "uvm_macros.svh";
import uvm_pkg::*;


module testbench;


    logic CLK = 0;
   	reset_if                           reset(CLK);
 	intel_mac_seg_if #(test::SEGMENTS) rx_mac_seg(CLK);
	mfb_if #(test::REGIONS, test::REGION_SIZE, 8, 8, 1) tx_mac_seg(CLK);

    always #(test::CLK_PERIOD/2) CLK = ~CLK;
    assign rx_mac_seg.READY = 1'b1;


    RX_MAC_LITE_ADAPTER_MAC_SEG  #(
        .REGIONS      (test::REGIONS),
        .REGION_SIZE  (test::REGION_SIZE),
        .SEGMENTS     (test::SEGMENTS)
    )
    DUT (
        .CLK              (CLK),
        .RESET            (reset.dut.RESET),
        // INPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
        .IN_MAC_DATA      (rx_mac_seg.dut_rx.DATA),
        .IN_MAC_INFRAME   (rx_mac_seg.dut_rx.INFRAME),
        .IN_MAC_EOP_EMPTY (rx_mac_seg.dut_rx.EOP_EMPTY),
        .IN_MAC_FCS_ERROR (rx_mac_seg.dut_rx.FCS_ERROR),
        .IN_MAC_ERROR     (rx_mac_seg.dut_rx.ERROR),
        .IN_MAC_STATUS    (rx_mac_seg.dut_rx.STATUS_DATA),
        .IN_MAC_VALID     (rx_mac_seg.dut_rx.VALID),
        // OUTPUT MFB INTERFACE
        // (RX MAC LITE, allowed MFB configurations: REGIONS,REGION_SIZE,8,8
        .OUT_MFB_DATA     (tx_mac_seg.dut_tx.DATA),
        .OUT_MFB_SOF      (tx_mac_seg.dut_tx.SOF),
        .OUT_MFB_SOF_POS  (tx_mac_seg.dut_tx.SOF_POS),
        .OUT_MFB_EOF      (tx_mac_seg.dut_tx.EOF),
        .OUT_MFB_EOF_POS  (tx_mac_seg.dut_tx.EOF_POS),
        .OUT_MFB_ERROR    (tx_mac_seg.dut_tx.META),
        .OUT_MFB_SRC_RDY  (tx_mac_seg.dut_tx.SRC_RDY),
        .OUT_LINK_UP      ()
    );

    mac_rx_property #(
        .REGIONS      (test::REGIONS),
        .REGION_SIZE  (test::REGION_SIZE),
        .BLOCK_SIZE   (8),
        .ITEM_WIDTH   (8),
        .META_WIDTH   (1)
    )
    PROPERTY_CHECK (
        .RESET   (reset.dut.RESET),
        .mfb_vif (tx_mac_seg)
    );


    initial begin
        uvm_root m_root;

        uvm_config_db#(virtual reset_if)::set(null, "", "RESET_IF", reset);
        uvm_config_db#(virtual intel_mac_seg_if #(test::SEGMENTS))::set(null, "", "RX_MAC_SEQ_IF", rx_mac_seg);
        uvm_config_db#(virtual mfb_if #(test::REGIONS, test::REGION_SIZE, 8, 8, 1))::set(null, "", "TX_MAC_SEQ_IF", tx_mac_seg);

        m_root = uvm_root::get();
        m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);
        m_root.finish_on_completion = 0;

        uvm_config_db#(int)            ::set(null, "", "recording_detail", 0);
        uvm_config_db#(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

        run_test();
        $stop(2);
    end

endmodule
