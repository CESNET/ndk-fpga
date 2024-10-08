/*
 * DUT.sv: Design under test
 * Copyright (C) 2012 CESNET
 * Author(s): Pavel Benacek <benacek@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkURx.dut    RX[PORTS],
   iFrameLinkURx.dut    RXHDR[PORTS],
   iFrameLinkUTx.dut    TX,
   iFrameLinkUTx.dut    TXHDR
);

// Signals for DUT conection
    // Data
wire [(PORTS*DATA_WIDTH)-1:0] rx_data;
wire [(PORTS*SOP_POS_WIDTH)-1:0] rx_sop_pos;
wire [(PORTS*EOP_POS_WIDTH)-1:0] rx_eop_pos;
wire [PORTS-1:0] rx_sop;
wire [PORTS-1:0] rx_eop;
wire [PORTS-1:0] rx_src_rdy;
wire [PORTS-1:0] rx_dst_rdy;
    // RX Header
wire [(PORTS*HDR_WIDTH)-1:0] rx_hdr_data;
wire [PORTS-1:0] rx_hdr_src_rdy;
wire [PORTS-1:0] rx_hdr_dst_rdy;
    // TX header
wire [HDR_WIDTH-1:0] tx_hdr_data;
wire tx_hdr_src_rdy;
wire tx_hdr_dst_rdy;
genvar i;

// Connecting RX to interfaces
generate
for (i=0; i<PORTS; i++) begin
    // Data
  assign rx_data[(i+1)*DATA_WIDTH-1:DATA_WIDTH*i] = RX[i].DATA;
  assign rx_sop_pos[(i+1)*SOP_POS_WIDTH-1:SOP_POS_WIDTH*i] = RX[i].SOP_POS;
  assign rx_eop_pos[(i+1)*EOP_POS_WIDTH-1:EOP_POS_WIDTH*i] = RX[i].EOP_POS;
  assign rx_sop[i] = RX[i].SOP;
  assign rx_eop[i] = RX[i].EOP;
  assign rx_src_rdy[i] = RX[i].SRC_RDY;
  assign RX[i].DST_RDY = rx_dst_rdy[i];

    // Header
  assign rx_hdr_data[(i+1)*HDR_WIDTH-1:HDR_WIDTH*i] = RXHDR[i].DATA;
  assign rx_hdr_src_rdy[i] = RXHDR[i].SRC_RDY;
  assign RXHDR[i].DST_RDY = rx_hdr_dst_rdy[i];
end
endgenerate

// Connecting header interface to TX (default values - we are transfering one word only)
assign TXHDR.SOP = 1;
assign TXHDR.EOP = 1;
assign TXHDR.SOP_POS = 0;
assign TXHDR.EOP_POS = {HDR_EOP_POS_WIDTH {1'b1}};
    // Header data and src/dst ready signals
assign TXHDR.DATA = tx_hdr_data;
assign TXHDR.SRC_RDY = tx_hdr_src_rdy;
assign tx_hdr_dst_rdy = TXHDR.DST_RDY;

// -------------------- Module body -------------------------------------------
FLUA_BINDER_10_EFF #(
     .DATA_WIDTH(DATA_WIDTH),
     .SOP_POS_WIDTH(SOP_POS_WIDTH),
     .DIVISION_RATIO(DIVISION_RATIO),
     .PIPELINE_MAP(PIPELINE_MAP),
     .HDR_ENABLE(HDR_ENABLE),
     .HDR_INSERT(HDR_INSERT),
     .HDR_WIDTH(HDR_WIDTH),
     .HDR_FIFO_ITEMS(HDR_FIFO_ITEMS),
     .RESERVE_GAP_EN(RESERVE_GAP_EN),
     .ENABLE_DEBUG(ENABLE_DEBUG),
     .DSP_MAP(DSP_MAP)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // RX Port
     .RX_DATA     (rx_data),
     .RX_SOP_POS  (rx_sop_pos),
     .RX_EOP_POS  (rx_eop_pos),
     .RX_SOP      (rx_sop),
     .RX_EOP      (rx_eop),
     .RX_SRC_RDY  (rx_src_rdy),
     .RX_DST_RDY  (rx_dst_rdy),

     .RX_HDR_DATA       (rx_hdr_data),
     .RX_HDR_SRC_RDY    (rx_hdr_src_rdy),
     .RX_HDR_DST_RDY    (rx_hdr_dst_rdy),

    // TX Port
     .TX_DATA     (TX.DATA),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY),

     .TX_HDR_DATA       (tx_hdr_data),
     .TX_HDR_SRC_RDY    (tx_hdr_src_rdy),
     .TX_HDR_DST_RDY    (tx_hdr_dst_rdy)
);

endmodule : DUT
