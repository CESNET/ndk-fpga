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
   iFrameLinkURx.dut RX[PORTS],
   iFrameLinkUTx.dut TX
);

// Signals for DUT conection
wire [(PORTS*DATA_WIDTH)-1:0] rx_data;
wire [(PORTS*SOP_POS_WIDTH)-1:0] rx_sop_pos;
wire [(PORTS*EOP_POS_WIDTH)-1:0] rx_eop_pos;
wire [PORTS-1:0] rx_sop;
wire [PORTS-1:0] rx_eop;
wire [PORTS-1:0] rx_src_rdy;
wire [PORTS-1:0] rx_dst_rdy;
genvar i;

// Connecting TX to interfaces
generate
for (i=0; i<PORTS; i++) begin
  assign rx_data[(i+1)*DATA_WIDTH-1:DATA_WIDTH*i] = RX[i].DATA;
  assign rx_sop_pos[(i+1)*SOP_POS_WIDTH-1:SOP_POS_WIDTH*i] = RX[i].SOP_POS;
  assign rx_eop_pos[(i+1)*EOP_POS_WIDTH-1:EOP_POS_WIDTH*i] = RX[i].EOP_POS;
  assign rx_sop[i] = RX[i].SOP;
  assign rx_eop[i] = RX[i].EOP;
  assign rx_src_rdy[i] = RX[i].SRC_RDY;
  assign RX[i].DST_RDY = rx_dst_rdy[i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
flu_binder #(
     .DATA_WIDTH(DATA_WIDTH),
     .SOP_POS_WIDTH(SOP_POS_WIDTH),
     .INPUT_PORTS(PORTS)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Port 0
     .RX_DATA     (rx_data),
     .RX_SOP_POS  (rx_sop_pos),
     .RX_EOP_POS  (rx_eop_pos),
     .RX_SOP      (rx_sop),
     .RX_EOP      (rx_eop),
     .RX_SRC_RDY  (rx_src_rdy),
     .RX_DST_RDY  (rx_dst_rdy),

    // Port 0
     .TX_DATA     (TX.DATA),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY)
);


endmodule : DUT
