/*
 * mi32_ifc.pkg: MI32 Interface
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *            Petr Kastovsky <kastovsky@liberouter.org>
 *            Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                         MI32 Interface declaration
// ----------------------------------------------------------------------------
// enum that defines local constants for mi32 interface
// -- MI32 Interface -----------------------------------------------------
interface iMi32 (input logic CLK, RESET);
  logic [31:0] ADDR  = 0;  // ADDRess
  logic [31:0] DWR   = 0;  // Data to be WRitten
  logic [31:0] DRD;        // Data to be ReaD
  logic [3:0] BE     = 0;  // Byte Enable
  logic RD           = 0;  // ReaD request
  logic WR           = 0;  // WRite request
  logic ARDY;              // Address ReaDY
  logic DRDY;              // Data ReaDY

  //-- MI32 Clocking Blocks ---------------------------------------------------
  clocking cb @(posedge CLK);
    input  ARDY, DRDY, DRD;
    output ADDR, DWR, BE, RD, WR;
  endclocking: cb;

  clocking monitor_cb @(posedge CLK);
    input ADDR, DWR, DRD, BE, RD, WR, ARDY, DRDY;
  endclocking: monitor_cb;

  //-- MI32 Modports ----------------------------------------------------------
  modport dut (input  ADDR,
               input  DWR,
               input  BE,
               input  RD,
               input  WR,
               output ARDY,
               output DRDY,
               output DRD);

  // Driver Modport
  modport tb (clocking cb);

  // Monitor Modport
  modport monitor (clocking monitor_cb);

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

endinterface : iMi32
