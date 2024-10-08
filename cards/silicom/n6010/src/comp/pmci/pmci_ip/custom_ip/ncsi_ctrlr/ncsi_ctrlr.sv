// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// NCSI controller controls the NCSI RBT interface. The NCSI control traffic
// received from host is forwarded to PMCI-Nios and pass through taffic to AFU's 
// packet filter block. Similarly, the control traffic from PMCI-Nios and pass 
// through traffic from AFU's packet filter is muxed and forwarded to host over 
// RBT interface.
//-----------------------------------------------------------------------------

module ncsi_ctrlr (
   input  logic                        clk,
   input  logic                        reset,

   //NCSI-RBT Interface Signals
   input  logic                        ncsi_clk,
   input  logic [1:0]                  ncsi_txd,
   input  logic                        ncsi_tx_en,
   output logic [1:0]                  ncsi_rxd,
   output logic                        ncsi_crs_dv,
   input  logic                        ncsi_arb_in,
   output logic                        ncsi_arb_out
);

//-----------------------------------------------------------------------------
// NCSI RBT Loopback until we implement NCSI feature
//-----------------------------------------------------------------------------
assign ncsi_rxd      = ncsi_txd;
assign ncsi_crs_dv   = ncsi_tx_en;
assign ncsi_arb_out  = ncsi_arb_in;

endmodule 
