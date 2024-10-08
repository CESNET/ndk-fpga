/*
 * DUT.sv: Design under test
 * Copyright (C) 2014 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkURx.dut RX,
   iFrameLinkURx.dut HDR,
   iFrameLinkUTx.dut TX
);

wire [DATA_WIDTH-1:0] tx_data;
wire [2:0] tx_channel;
wire [SOP_POS_WIDTH-1:0] tx_sop_pos;
wire [EOP_POS_WIDTH-1:0] tx_eop_pos;
wire tx_sop;
wire tx_eop;
wire tx_src_rdy;
wire tx_dst_rdy;

// -------------------- Module body -------------------------------------------
HINS_PLUS #(
     .DATA_WIDTH    (DATA_WIDTH),
     .SOP_POS_WIDTH (SOP_POS_WIDTH),
     .HDR_WIDTH     (HDR_WIDTH),
     .RX_CHANNELS   (8)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Write Port
     .RX_DATA     (RX.DATA),
     .RX_CHANNEL  (HDR.DATA[2:0]),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

     .HDR_DATA    (HDR.DATA),
     .HDR_READY   (HDR.SRC_RDY),
     .HDR_NEXT    (HDR.DST_RDY),

    // Read Port
     .TX_DATA     (tx_data),
     .TX_CHANNEL  (tx_channel),
     .TX_SOP_POS  (tx_sop_pos),
     .TX_EOP_POS  (tx_eop_pos),
     .TX_SOP      (tx_sop),
     .TX_EOP      (tx_eop),
     .TX_SRC_RDY  (tx_src_rdy),
     .TX_DST_RDY  (tx_dst_rdy)
);

FLU_PIPE_PLUS #(
     .DATA_WIDTH     (DATA_WIDTH),
     .SOP_POS_WIDTH  (SOP_POS_WIDTH),
     .USE_OUTREG     (1),
     .FAKE_PIPE      (0),
     .CHANNEL_WIDTH  (3)
   )

   VHDL_PIPE_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Write Port
     .RX_DATA     (tx_data),
     .RX_CHANNEL  (tx_channel),
     .RX_SOP_POS  (tx_sop_pos),
     .RX_EOP_POS  (tx_eop_pos),
     .RX_SOP      (tx_sop),
     .RX_EOP      (tx_eop),
     .RX_SRC_RDY  (tx_src_rdy),
     .RX_DST_RDY  (tx_dst_rdy),

    // Read Port
     .TX_DATA     (TX.DATA),
     .TX_CHANNEL  (),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY)
);


endmodule : DUT
