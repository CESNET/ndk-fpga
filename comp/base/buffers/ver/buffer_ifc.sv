/*
 * buffer_ifc.sv: General Interface
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */


// ----------------------------------------------------------------------------
//                         Interface declaration
// ----------------------------------------------------------------------------

// -- General Interface -----------------------------------------------------
interface iNFifoTx #( DATA_WIDTH=64, FLOWS=2, BLOCK_SIZE= 512, LUT_MEMORY=0, GLOB_STATE=0) (input logic CLK, RESET);

  import math_pkg::*;       // log2()

  //-- Signals ----------------------------------------------

  // Write Signals
  logic [DATA_WIDTH-1:0] DATA_IN                = 0;  // Input Data1
  logic WRITE                                   = 0;  // Write Signal
  logic [$clog2(BLOCK_SIZE)-1:0]WR_ADDR          = 0;  // Write Address to Memory
  logic [$clog2(BLOCK_SIZE+1)*FLOWS-1:0] NEW_LEN = 0;  // Number of items to be marked as occuppied/valid
  logic [FLOWS-1:0] NEW_LEN_DV                  = 0;  // Valid signal for NEW_LEN

  // Flow Signal
  logic [math_pkg::abs($clog2(FLOWS)-1):0] BLOCK_ADDR     = 0;  // Number of Flow

  // Read Signals
  logic [DATA_WIDTH/FLOWS-1:0] DATA_OUT;              // Output Data
  logic DATA_VLD;                                     // Valid Signal for Output Data
  logic READ                                    = 0;  // Read Signal

  // Control Signals
  logic EMPTY;                                        // No valid Data are available on Output
  logic [FLOWS-1:0] FULL;                             // No more Data can be stored in component
  logic [$clog2(BLOCK_SIZE+1)-1:0] STATUS;            // Number of items that are in memory
  logic [$clog2(BLOCK_SIZE+1)*FLOWS-1:0] STATUS_F;

  //-- Clocking Blocks ---------------------------------------

  // Clocking Block fifo_write
  clocking fifo_write_cb @(posedge CLK);
        input FULL;
        output DATA_IN, BLOCK_ADDR, WRITE;
  endclocking: fifo_write_cb;

  // Clocking Block nfifo_read
  clocking nfifo_read_cb @(posedge CLK);
        output READ;
        input DATA_OUT, DATA_VLD, EMPTY, STATUS;
  endclocking: nfifo_read_cb;

  // Clocking Block nfifo_monitor
  clocking nfifo_monitor_cb @(posedge CLK);
        input DATA_OUT, DATA_VLD, READ, EMPTY, STATUS;
  endclocking: nfifo_monitor_cb;

  // Clocking Block mem_write
  clocking mem_write_cb @(posedge CLK);
        input FULL, STATUS_F;
        output DATA_IN, BLOCK_ADDR, WR_ADDR, NEW_LEN, NEW_LEN_DV, WRITE;
  endclocking: mem_write_cb;


  //-- Modports ----------------------------------------------

  // Fifo Write Modport
  modport fifo_write    (input  DATA_IN,
                         input  BLOCK_ADDR,
                         input  WRITE,
                         output FULL);

  // nFifo Read Modport
  modport nfifo_read    (output DATA_OUT,
                         output DATA_VLD,
                         input  READ,
                         output EMPTY,
                         output STATUS);

  // Memory Read Modport
  modport mem_write     (input  DATA_IN,
                         input  BLOCK_ADDR,
                         input  WR_ADDR,
                         input  NEW_LEN,
                         input  NEW_LEN_DV,
                         input  WRITE,
                         output FULL,
                         output STATUS_F
                         );


  //-- Transitive Modports -----------------------------------

  modport fifo_write_tb (clocking fifo_write_cb);
  modport nfifo_read_tb (clocking nfifo_read_cb);
  modport nfifo_monitor (clocking nfifo_monitor_cb);
  modport mem_write_tb  (clocking mem_write_cb);

endinterface : iNFifoTx


// -- nFifoRx Interface -----------------------------------------------------
interface iNFifoRx #( DATA_WIDTH=64, FLOWS=2, BLOCK_SIZE= 512, LUT_MEMORY=0, GLOB_STATE=0) (input logic CLK, RESET);


  //-- Signals ----------------------------------------------

  // Write Signals
  logic [DATA_WIDTH/FLOWS-1:0] DATA_IN          = 0;  // Input Data2
  logic WRITE                                   = 0;  // Write Signal

  // Flow Signal
  logic [math_pkg::abs($clog2(FLOWS)-1):0] BLOCK_ADDR     = 0;  // Number of Flow

  // Read Signals
  logic [DATA_WIDTH-1:0] DATA_OUT;                    // Output Data
  logic DATA_VLD;                                     // Valid Signal for Output Data
  logic READ                                    = 0;  // Read Signal
  logic PIPE_EN                                 = 0;  // Pipeline enable to Memory
  logic [$clog2(BLOCK_SIZE)-1:0] RD_ADDR         = 0;  // Read Address to Memory
  logic [$clog2(BLOCK_SIZE+1)*FLOWS-1:0] REL_LEN = 0;  // Number of items to be released
  logic [FLOWS-1:0]REL_LEN_DV                   = 0;  // Valid Signal for REL_LEN


  // Control Signals
  logic [FLOWS-1:0] EMPTY;                            // No valid Data are available on Output
  logic FULL;                                         // No more Data can be stored in component
  logic [$clog2(BLOCK_SIZE+1)*FLOWS-1:0] STATUS;      // Number of items that are in memory


  //-- Clocking Blocks ---------------------------------------

  // Clocking Block nfifo_write
  clocking nfifo_write_cb @(posedge CLK);
        input FULL;
        output DATA_IN, WRITE;
  endclocking: nfifo_write_cb;

  // Clocking Block fifo_read
  clocking fifo_read_cb @(posedge CLK);
        output READ, PIPE_EN, BLOCK_ADDR;
        input DATA_OUT, DATA_VLD, EMPTY, STATUS;
  endclocking: fifo_read_cb;

  // Clocking Block fifo_monitor
  clocking fifo_monitor_cb @(posedge CLK);
        input DATA_OUT, DATA_VLD, READ, PIPE_EN, EMPTY, STATUS, BLOCK_ADDR;
  endclocking: fifo_monitor_cb;

  // Clocking Block mem_read
  clocking mem_read_cb @(posedge CLK);
        input DATA_OUT, DATA_VLD, EMPTY, STATUS, BLOCK_ADDR, RD_ADDR, REL_LEN, REL_LEN_DV;
        output READ, PIPE_EN;
  endclocking: mem_read_cb;

  // Clocking Block mem_monitor
  clocking mem_monitor_cb @(posedge CLK);
        input DATA_OUT, DATA_VLD, EMPTY, STATUS, READ, PIPE_EN;
        output  REL_LEN, REL_LEN_DV, BLOCK_ADDR, RD_ADDR;
  endclocking: mem_monitor_cb;


  //-- Modports ----------------------------------------------

  // nFifo Write Modport
  modport nfifo_write   (input  DATA_IN,
                         input  WRITE,
                         output FULL);

  // Fifo Read Modport
  modport fifo_read     (output DATA_OUT,
                         output DATA_VLD,
                         input  BLOCK_ADDR,
                         input  READ,
                         input  PIPE_EN,
                         output EMPTY,
                         output STATUS);

  // Memory Read Modport
  modport mem_read      (output DATA_OUT,
                         output DATA_VLD,
                         input  BLOCK_ADDR,
                         input  RD_ADDR,
                         input  READ,
                         input  REL_LEN,
                         input  REL_LEN_DV,
                         input  PIPE_EN,
                         output EMPTY,
                         output STATUS);


  modport nfifo_write_tb(clocking nfifo_write_cb);
  modport fifo_read_tb  (clocking fifo_read_cb);
  modport fifo_monitor  (clocking fifo_monitor_cb);
  modport mem_read_tb   (clocking mem_read_cb);
  modport mem_monitor   (clocking mem_monitor_cb);

endinterface : iNFifoRx


// -- Memory Interface -------------------------------------------------------
interface iMemRead #(DATA_WIDTH=64, FLOWS=2, BLOCK_SIZE= 512)
                                               (input logic CLK, RESET);

  import math_pkg::*;       // log2()

  //-- Signals ----------------------------------------------

  // Memory Read Signals
  logic [DATA_WIDTH-1:0]       DATA_OUT;       // Output Data
  logic                        DATA_VLD;       // Valid Signal for Output Data
  logic                        READ    = 0;    // Read Signal
  logic                        PIPE_EN = 0;    // Pipeline enable to Memory
  logic [math_pkg::abs($clog2(FLOWS)-1):0] BLOCK_ADDR = 0; // Number of Flow
  logic [$clog2(BLOCK_SIZE)-1:0] RD_ADDR = 0;    // Read Address to Memory
  logic [$clog2(BLOCK_SIZE+1)*FLOWS-1:0] REL_LEN = 0; // Number of items to be released
  logic [FLOWS-1:0]            REL_LEN_DV = 0; // Valid Signal for REL_LEN


  // Control Signals
  logic [FLOWS-1:0]            EMPTY;  // No valid Data are available on Output
  logic [$clog2(BLOCK_SIZE+1)*FLOWS-1:0] STATUS; // Number of items in memory


  //-- Clocking Blocks ---------------------------------------

  // Clocking Block
  clocking cb @(posedge CLK);
    input  DATA_OUT, DATA_VLD, EMPTY, STATUS;
    output BLOCK_ADDR, RD_ADDR, REL_LEN, REL_LEN_DV, READ, PIPE_EN;
  endclocking: cb;


  //-- Modports ----------------------------------------------

  // DUT modport
  modport dut (output DATA_OUT,
               output DATA_VLD,
               input  BLOCK_ADDR,
               input  RD_ADDR,
               input  READ,
               input  REL_LEN,
               input  REL_LEN_DV,
               input  PIPE_EN,
               output EMPTY,
               output STATUS);


  // Testbench  modport
  modport tb (clocking cb);

endinterface : iMemRead
