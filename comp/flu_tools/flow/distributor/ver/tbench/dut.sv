/*
 * DUT.sv: Design under test
 * Copyright (C) 2012 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
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
   inumInterface.dut INUM,
   iFrameLinkURx.dut RX,
   iFrameLinkUTx.dut TX[PORTS]
);

// Signals for DUT conection
wire [(PORTS*DATA_WIDTH)-1:0] tx_data;
wire [(PORTS*SOP_POS_WIDTH)-1:0] tx_sop_pos;
wire [(PORTS*EOP_POS_WIDTH)-1:0] tx_eop_pos;
wire [PORTS-1:0] tx_sop;
wire [PORTS-1:0] tx_eop;
wire [PORTS-1:0] tx_src_rdy;
wire [PORTS-1:0] tx_dst_rdy;
genvar i;

// Connecting TX to interfaces
generate
for (i=0; i<PORTS; i++) begin
  assign TX[i].DATA  = tx_data[(i+1)*DATA_WIDTH-1:DATA_WIDTH*i];
  assign TX[i].SOP_POS  = tx_sop_pos[(i+1)*SOP_POS_WIDTH-1:SOP_POS_WIDTH*i];
  assign TX[i].EOP_POS  = tx_eop_pos[(i+1)*EOP_POS_WIDTH-1:EOP_POS_WIDTH*i];
  assign TX[i].SOP = tx_sop[i];
  assign TX[i].EOP = tx_eop[i];
  assign TX[i].SRC_RDY = tx_src_rdy[i];
  assign tx_dst_rdy[i] = TX[i].DST_RDY;
  end
endgenerate

// -------------------- Module body -------------------------------------------
flu_distributor #(
     .DATA_WIDTH(DATA_WIDTH),
     .SOP_POS_WIDTH(SOP_POS_WIDTH),
     .OUTPUT_PORTS(PORTS)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Port 0
     .RX_DATA     (RX.DATA),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

    // Port 0
     .TX_DATA     (tx_data),
     .TX_SOP_POS  (tx_sop_pos),
     .TX_EOP_POS  (tx_eop_pos),
     .TX_SOP      (tx_sop),
     .TX_EOP      (tx_eop),
     .TX_SRC_RDY  (tx_src_rdy),
     .TX_DST_RDY  (tx_dst_rdy),

     .INUM_MASK  (INUM.INUM_MASK),
     .INUM_READY (INUM.INUM_READY),
     .INUM_NEXT  (INUM.INUM_NEXT)
);


endmodule : DUT
