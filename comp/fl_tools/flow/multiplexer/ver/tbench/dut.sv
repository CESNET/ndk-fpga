/*
 * DUT.sv: Design under test
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
import math_pkg::*; // log2()

module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkRx.dut RX[CHANNELS],
   iFrameLinkTx.dut TX[CHANNELS]
);

// Signals for DUT conection
wire [(CHANNELS*DATA_WIDTH)-1:0] rx_data;
wire [(CHANNELS*DREM_WIDTH)-1:0] rx_drem;
wire [CHANNELS-1:0] rx_sof_n;
wire [CHANNELS-1:0] rx_eof_n;
wire [CHANNELS-1:0] rx_sop_n;
wire [CHANNELS-1:0] rx_eop_n;
wire [CHANNELS-1:0] rx_src_rdy_n;
wire [CHANNELS-1:0] rx_dst_rdy_n;

wire [DATA_WIDTH-1:0] tx_data;
wire [DREM_WIDTH-1:0] tx_drem;
wire tx_sof_n;
wire tx_eof_n;
wire tx_sop_n;
wire tx_eop_n;
wire tx_src_rdy_n;
logic [CHANNELS-1:0]      tx_src_rdy_n_vec;
wire [CHANNELS-1:0]       tx_dst_rdy_n;
wire [log2(CHANNELS)-1:0] tx_channel;

// Connecting RX to interfaces
generate
for (genvar i=0; i<CHANNELS; i++) begin
  assign rx_data[(i+1)*DATA_WIDTH-1:DATA_WIDTH*i] = RX[i].DATA;
  assign rx_drem[(i+1)*DREM_WIDTH-1:DREM_WIDTH*i] = RX[i].DREM;
  assign rx_sof_n[i] = RX[i].SOF_N;
  assign rx_eof_n[i] = RX[i].EOF_N;
  assign rx_sop_n[i] = RX[i].SOP_N;
  assign rx_eop_n[i] = RX[i].EOP_N;
  assign rx_src_rdy_n[i] = RX[i].SRC_RDY_N;
  assign RX[i].DST_RDY_N = rx_dst_rdy_n[i];

  assign TX[i].DATA  = tx_data[DATA_WIDTH-1:0];
  assign TX[i].DREM  = tx_drem[DREM_WIDTH-1:0];
  assign TX[i].SOF_N = tx_sof_n;
  assign TX[i].EOF_N = tx_eof_n;
  assign TX[i].SOP_N = tx_sop_n;
  assign TX[i].EOP_N = tx_eop_n;
  assign TX[i].SRC_RDY_N = tx_src_rdy_n_vec[i];
  assign tx_dst_rdy_n[i] = TX[i].DST_RDY_N;

end
endgenerate

always_comb begin
  tx_src_rdy_n_vec <= '1;
  tx_src_rdy_n_vec[tx_channel] <= tx_src_rdy_n;
end

// -------------------- Module body -------------------------------------------
FL_MULTIPLEXER #(
     .DATA_WIDTH       (DATA_WIDTH),
     .CHANNELS         (CHANNELS)
      )
   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // RX ports
     .RX_DATA       (rx_data),
     .RX_DREM       (rx_drem),
     .RX_SOF_N      (rx_sof_n),
     .RX_EOF_N      (rx_eof_n),
     .RX_SOP_N      (rx_sop_n),
     .RX_EOP_N      (rx_eop_n),
     .RX_SRC_RDY_N  (rx_src_rdy_n),
     .RX_DST_RDY_N  (rx_dst_rdy_n),

    // TX port
     .TX_DATA       (tx_data),
     .TX_DREM       (tx_drem),
     .TX_SOF_N      (tx_sof_n),
     .TX_EOF_N      (tx_eof_n),
     .TX_SOP_N      (tx_sop_n),
     .TX_EOP_N      (tx_eop_n),
     .TX_SRC_RDY_N  (tx_src_rdy_n),
     .TX_DST_RDY_N  (tx_dst_rdy_n),
     .TX_CHANNEL    (tx_channel)
);


endmodule : DUT
