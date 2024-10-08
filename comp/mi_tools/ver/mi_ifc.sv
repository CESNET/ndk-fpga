/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                          MI Interface declaration
// ----------------------------------------------------------------------------
interface iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH = 0) (input wire logic CLK, RESET);
  wire logic [ADDR_WIDTH-1:0]    ADDR;  // ADDRess
  wire logic [DATA_WIDTH-1:0]    DWR;   // Data to be WRitten
  wire logic [META_WIDTH-1:0]    MWR;   // META to be WRitten
  wire logic [DATA_WIDTH/8-1:0]  BE;    // Byte Enable
  wire logic RD;           // ReaD request
  wire logic WR;           // WRite request

  logic ARDY;              // Address ReaDY
  logic DRDY;              // Data ReaDY
  logic [DATA_WIDTH-1:0]    DRD;   // Data to be ReaD

  //-- MI32 Clocking Blocks ---------------------------------------------------

  clocking monitor_cb @(posedge CLK);
    input ADDR, DWR, MWR, DRD, BE, RD, WR, ARDY, DRDY;
  endclocking: monitor_cb;

  clocking cb_master @(posedge CLK);
    output  ADDR, DWR, MWR, BE, RD, WR; input RESET, ARDY, DRDY, DRD;
  endclocking;

  //-- MI32 Modports ----------------------------------------------------------
  modport slave  (input   ADDR, DWR, MWR, BE, RD, WR, output ARDY, DRDY, DRD);
  modport master (output  ADDR, DWR, MWR, BE, RD, WR, input ARDY, DRDY, DRD);

  modport tb_slave  (input   ADDR, DWR, MWR, BE, RD, WR, CLK, RESET, output ARDY, DRDY, DRD);
  modport tb_master (clocking cb_master);

  //verification modports
  modport monitor   (clocking monitor_cb);

  property valid;
      @(posedge CLK) disable iff(RESET)
      !$isunknown(RD) && !$isunknown(WR);
  endproperty

  property valid_request;
     @(posedge CLK) disable iff(RESET)
     (RD || WR) |-> (!$isunknown(ADDR) && !$isunknown(BE));
  endproperty

  property valid_request_write_data;
     @(posedge CLK) disable iff(RESET)
     (WR) |-> (!$isunknown(DWR));
  endproperty

  property valid_request_write_meta;
     @(posedge CLK) disable iff(RESET)
     ((RD || WR) && META_WIDTH > 0) |-> (!$isunknown(MWR));
  endproperty

  property valid_response;
     @(posedge CLK) disable iff(RESET)
     (DRDY) |-> (!$isunknown(DRD));
  endproperty

  assert property (valid) else begin $error("signlas RD and WR have to be allways valid"); $stop(); end
  assert property (valid_request) else begin $error("signal addr and be have to be valid when RD or WR signal is asserted"); $stop(); end
  assert property (valid_request_write_data) else begin $error("when signal WR is asserted then signal DWR have to be valid"); $stop(); end
  assert property (valid_request_write_meta) else begin $error("when signal WR is asserted and META_WIDTH > 0 then signal MWR have to be valid"); $stop(); end
  assert property (valid_response) else begin $error("when signal DRDY is asserted then signal DRD have to be valid"); $stop(); end
  // --------------------------------------------------------------------------
  // -- Interface properties/assertions
  // --------------------------------------------------------------------------
  // -- While RESET RD inactive ----------------------------------------
  // RD may be active only if RESET is inactive.
  property RESETR;
     @(posedge CLK) (RESET)|->(not RD);
  endproperty

  assert property (RESETR)
     else $error("RD is active during reset.");

  // -- While RESET WR inactive ----------------------------------------
  // WR may be active only if RESET is inactive.
  property RESETW;
     @(posedge CLK) (RESET)|->(not WR);
  endproperty

  assert property (RESETW)
     else $error("WR is active during reset.");

  // -- WR never together with RD ---------------------------------------
  // WR can not be active together with RD.
  property RDnottogetherWR;
     @(posedge CLK) (RD)|->(!WR);
  endproperty

  assert property (RDnottogetherWR)
     else $error("RD and WR signals can not be active at the same cycle.");

endinterface
