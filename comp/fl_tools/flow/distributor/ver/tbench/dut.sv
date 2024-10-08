/*
 * DUT.sv: Design under test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
   iFrameLinkRx.dut RX,
   iFrameLinkTx.dut TX[OUTPUT_COUNT]
);

// Signals for DUT conection
wire [(OUTPUT_COUNT*DATA_WIDTH)-1:0] tx_data;
wire [(OUTPUT_COUNT*DREM_WIDTH)-1:0] tx_drem;
wire [OUTPUT_COUNT-1:0] tx_sof_n;
wire [OUTPUT_COUNT-1:0] tx_eof_n;
wire [OUTPUT_COUNT-1:0] tx_sop_n;
wire [OUTPUT_COUNT-1:0] tx_eop_n;
wire [OUTPUT_COUNT-1:0] tx_src_rdy_n;
wire [OUTPUT_COUNT-1:0] tx_dst_rdy_n;
genvar i;

// Connecting TX to interfaces
generate
for (i=0; i<OUTPUT_COUNT; i++) begin
  assign TX[i].DATA  = tx_data[(i+1)*DATA_WIDTH-1:DATA_WIDTH*i];
  assign TX[i].DREM  = tx_drem[(i+1)*DREM_WIDTH-1:DREM_WIDTH*i];
  assign TX[i].SOF_N = tx_sof_n[i];
  assign TX[i].EOF_N = tx_eof_n[i];
  assign TX[i].SOP_N = tx_sop_n[i];
  assign TX[i].EOP_N = tx_eop_n[i];
  assign TX[i].SRC_RDY_N = tx_src_rdy_n[i];
  assign tx_dst_rdy_n[i] = TX[i].DST_RDY_N;
  end
endgenerate


// -------------------- Module body -------------------------------------------
FL_DISTRIBUTOR #(
     .DATA_WIDTH         (DATA_WIDTH),
     .INTERFACES_COUNT   (OUTPUT_COUNT),
     .DEFAULT_INTERFACE  (DEFAULT_IFC),
     .INUM_OFFSET        (INUM_OFFSET),
     .PARTS              (PARTS)
      )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // RX Port
     .RX_DATA       (RX.DATA),
     .RX_REM        (RX.DREM),
     .RX_SOF_N      (RX.SOF_N),
     .RX_EOF_N      (RX.EOF_N),
     .RX_SOP_N      (RX.SOP_N),
     .RX_EOP_N      (RX.EOP_N),
     .RX_SRC_RDY_N  (RX.SRC_RDY_N),
     .RX_DST_RDY_N  (RX.DST_RDY_N),

     // TX Port
     .TX_DATA       (tx_data),
     .TX_REM        (tx_drem),
     .TX_SOF_N      (tx_sof_n),
     .TX_EOF_N      (tx_eof_n),
     .TX_SOP_N      (tx_sop_n),
     .TX_EOP_N      (tx_eop_n),
     .TX_SRC_RDY_N  (tx_src_rdy_n),
     .TX_DST_RDY_N  (tx_dst_rdy_n)
);

endmodule : DUT
