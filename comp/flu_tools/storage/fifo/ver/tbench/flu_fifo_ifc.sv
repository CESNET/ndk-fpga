/*
 * flu_fifo_ifc.sv: FrameLink FIFO Control Interface
 * Copyright (C) 2012 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//           Frame Link Unaligned FIFO Control Interface declaration
// ----------------------------------------------------------------------------

// -- Frame Link Unaligned FIFO Control Interface -----------------------------
interface iFrameLinkUFifo #(STATUS_WIDTH = 8) (input logic CLK, RESET);
  // Control Interface
  logic LSTBLK                    ;   // Last block detection
  logic [STATUS_WIDTH-1:0] STATUS ;   // MSBs of exact number of free items in the FIFO
  logic EMPTY                     ;   // FIFO is empty
  logic FULL                      ;   // FIFO is full
  logic FRAME_RDY                 ;   // At least one whole frame is in the FIFO


  // Clocking blocks
  clocking ctrl_cb @(posedge CLK);
    input  LSTBLK, STATUS, EMPTY, FULL, FRAME_RDY;
  endclocking: ctrl_cb;

  // Control Modport
  modport ctrl (output  LSTBLK,
                output  STATUS,
                output  EMPTY,
                output  FULL,
                output  FRAME_RDY
               );

  modport ctrl_tb (clocking ctrl_cb);

endinterface : iFrameLinkUFifo
