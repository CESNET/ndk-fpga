// Copyright 2020 Intel Corporation
// SPDX-License-Identifier: MIT

// Description
//-----------------------------------------------------------------------------
//
//   A general purpose resynchronization module that uses the recommended altera_std_synchronizer
//   and altera_std_synchronizer_nocut synchronizer
//
//   Parameters:
//         SYNC_CHAIN_LENGTH
//               Length of the synchronizer chain for metastability retiming.
//         WIDTH
//               Number of bits to synchronize. Controls the width of the d and q ports.
//         INIT_VALUE
//               Initial values of the synchronization registers.
//         NO_CUT
//               0 : Enable embedded set_false path SDC
//               1 : DIsable embedded set_false_path SDC
//
//-----------------------------------------------------------------------------

`timescale 1ps / 1ps

module fim_resync #(
   parameter SYNC_CHAIN_LENGTH      = 2,  // Number of flip-flops for retiming. Must be >1
   parameter WIDTH                  = 1,  // Number of bits to resync
   parameter INIT_VALUE             = 0,
   parameter NO_CUT                 = 1,  // See description above
   parameter TURN_OFF_METASTABILITY = 1,  // Added metastability checker in simulation.  Disabled by default.
   parameter TURN_OFF_ADD_PIPELINE = 1
)(
   input  logic              clk,
   input  logic              reset,
   input  logic  [WIDTH-1:0] d,
   output logic  [WIDTH-1:0] q
);

localparam  INT_LEN       = (SYNC_CHAIN_LENGTH > 1) ? SYNC_CHAIN_LENGTH : 2;
localparam  L_INIT_VALUE  = (INIT_VALUE == 1) ? 1'b1 : 1'b0;

genvar ig;

// Generate a synchronizer chain for each bit
generate
   for(ig=0;ig<WIDTH;ig=ig+1) begin : resync_chains
      wire d_in;   // Input to sychronization chain.

      assign d_in = d[ig];

      if (NO_CUT == 0) begin
         wire sync_q_out;

         // Synchronizer with embedded set_false_path SDC
         altera_std_synchronizer #(
            .depth(INT_LEN)
         ) synchronizer (
            .clk      (clk),
            .reset_n  (~reset),
            .din      ((INIT_VALUE == 1) ? ~d_in : d_in),
            .dout     (sync_q_out)
         );

         if (TURN_OFF_ADD_PIPELINE == 1) begin: g_additional_pipeline_off
            assign q[ig] = (INIT_VALUE == 1) ? ~sync_q_out : sync_q_out;
         end
         else begin: g_additional_pipeline_on
            logic dup_tree_in = 1'(INIT_VALUE);
            always @(posedge clk) begin
               dup_tree_in <= (INIT_VALUE == 1) ? ~sync_q_out : sync_q_out;
            end

            fim_dup_tree
             #(
               .INIT_VALUE(INIT_VALUE)
               )
             dup
              (
               .clk,
               .din(dup_tree_in),
               .dout(q[ig])
               );
         end

         //synthesis translate_off
         initial begin
            synchronizer.dreg = {(INT_LEN-1){1'b0}};
            synchronizer.din_s1 = 1'b0;
         end
         //synthesis translate_on

      end else begin
         // Synchronizer WITHOUT embedded set_false_path SDC
         ofs_std_synchronizer_nocut #(
            .depth(INT_LEN),
            .rst_value(INIT_VALUE),
            .turn_off_meta(TURN_OFF_METASTABILITY),
            .turn_off_add_pipeline(TURN_OFF_ADD_PIPELINE)
         ) synchronizer_nocut (
            .clk      (clk),
            .reset_n  (~reset),
            .din      (d_in),
            .dout     (q[ig])
         );

         //synthesis translate_off
         initial begin
            synchronizer_nocut.dreg = {(INT_LEN-1){1'b0}};
            synchronizer_nocut.din_s1 = 1'b0;
         end
         //synthesis translate_on
      end
   end // for loop
endgenerate
endmodule
