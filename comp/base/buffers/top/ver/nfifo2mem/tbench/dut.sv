/*
 * DUT.sv: Design under test
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
//                        Module declaration
// ----------------------------------------------------------------------------
// obsahuje pouzite parametre
import test_pkg::*; // Test constants

module DUT (
   input logic CLK,
   input logic RESET,
   iNFifoRx.nfifo_write FW[FLOWS],
   iMemRead.dut         MR
);

// Signals for DUT conection
wire [DATA_WIDTH-1:0] fw_data_in;
wire [FLOWS-1:0] fw_write;
wire [FLOWS-1:0] fw_full;
genvar i;

// Connecting FW to interfaces
generate
for (i=0; i<FLOWS; i++) begin
  assign fw_data_in[(i+1)*(DATA_WIDTH/FLOWS)-1:(DATA_WIDTH/FLOWS)*i]    = FW[i].DATA_IN;
  assign fw_write[i]                                                    = FW[i].WRITE;
  assign FW[i].FULL                                                     = fw_full[i];
  end
endgenerate


// -------------------- Module body -------------------------------------------
NFIFO2MEM #(
        .DATA_WIDTH     (DATA_WIDTH),
        .FLOWS          (FLOWS),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .LUT_MEMORY     (LUT_MEMORY),
        .OUTPUT_REG     (OUTPUT_REG),
        .GLOB_STATE     (0)
   )

   VHDL_DUT_U (
    // Common Interface

    //vyber signalov
    .CLK               (CLK),
    .RESET             (RESET),

    // Write interface
    .DATA_IN            (fw_data_in),
    .WRITE              (fw_write),
    .FULL               (fw_full),

    // Read interface
    .DATA_OUT           (MR.DATA_OUT),
    .DATA_VLD           (MR.DATA_VLD),
    .BLOCK_ADDR         (MR.BLOCK_ADDR),
    .RD_ADDR            (MR.RD_ADDR),
    .READ               (MR.READ),
    .REL_LEN            (MR.REL_LEN),
    .REL_LEN_DV         (MR.REL_LEN_DV),
    .PIPE_EN            (MR.PIPE_EN),
    .EMPTY              (MR.EMPTY),

    .STATUS             (MR.STATUS)
    );

endmodule : DUT
