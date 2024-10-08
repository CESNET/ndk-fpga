/*
 * DUT.sv: Design under test
 * Copyright (C) 2008 CESNET
 * Author(s): Martin Kosek <kosek@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkRx.dut RX[INPUT_COUNT],
   iFrameLinkTx.dut TX
);

// Signals for DUT conection
wire [(INPUT_COUNT*INPUT_WIDTH)-1:0] rx_data;
wire [(INPUT_COUNT*INPUT_DREM_WIDTH)-1:0] rx_drem;
wire [INPUT_COUNT-1:0] rx_sof_n;
wire [INPUT_COUNT-1:0] rx_eof_n;
wire [INPUT_COUNT-1:0] rx_sop_n;
wire [INPUT_COUNT-1:0] rx_eop_n;
wire [INPUT_COUNT-1:0] rx_src_rdy_n;
wire [INPUT_COUNT-1:0] rx_dst_rdy_n;
genvar i;

// Connecting RX to interfaces
generate
for (i=0; i<INPUT_COUNT; i++) begin
  assign rx_data[(i+1)*INPUT_WIDTH-1:INPUT_WIDTH*i] = RX[i].DATA;
  assign rx_drem[(i+1)*INPUT_DREM_WIDTH-1:INPUT_DREM_WIDTH*i] = RX[i].DREM;
  assign rx_sof_n[i] = RX[i].SOF_N;
  assign rx_eof_n[i] = RX[i].EOF_N;
  assign rx_sop_n[i] = RX[i].SOP_N;
  assign rx_eop_n[i] = RX[i].EOP_N;
  assign rx_src_rdy_n[i] = RX[i].SRC_RDY_N;
  assign RX[i].DST_RDY_N = rx_dst_rdy_n[i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
FL_BINDER #(
     .INPUT_WIDTH       (INPUT_WIDTH),
     .OUTPUT_WIDTH      (OUTPUT_WIDTH),
     .INPUT_COUNT       (INPUT_COUNT),
     .FRAME_PARTS       (FRAME_PARTS),
     .LUT_MEMORY        (LUT_MEMORY),
     .LUT_BLOCK_SIZE    (LUT_BLOCK_SIZE),
     .SIMPLE_BINDER     (SIMPLE_BINDER),
     .STUPID_BINDER     (STUPID_BINDER)
      )
   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // RX ports
     .RX_DATA       (rx_data),
     .RX_REM        (rx_drem),
     .RX_SOF_N      (rx_sof_n),
     .RX_EOF_N      (rx_eof_n),
     .RX_SOP_N      (rx_sop_n),
     .RX_EOP_N      (rx_eop_n),
     .RX_SRC_RDY_N  (rx_src_rdy_n),
     .RX_DST_RDY_N  (rx_dst_rdy_n),

    // TX port
     .TX_DATA       (TX.DATA),
     .TX_REM        (TX.DREM),
     .TX_SOF_N      (TX.SOF_N),
     .TX_EOF_N      (TX.EOF_N),
     .TX_SOP_N      (TX.SOP_N),
     .TX_EOP_N      (TX.EOP_N),
     .TX_SRC_RDY_N  (TX.SRC_RDY_N),
     .TX_DST_RDY_N  (TX.DST_RDY_N)
);


endmodule : DUT
