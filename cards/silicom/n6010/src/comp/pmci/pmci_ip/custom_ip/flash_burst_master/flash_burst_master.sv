// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// This module converts single beat (4Byte/8Byte) flash read/write requests to 
// page read/write requests.
// Flash’s write performance improves when 256byte page program is used instead 
// of non-page program. Flash burst master aggregates contiguous 4B/8B flash 
// write requests from host and requests 256byte page write request to the 
// flash controller to improve flash write performance.
//-----------------------------------------------------------------------------

module flash_burst_master #(
   parameter   STAGING_AREA_BADDR   = 32'h0C80_0000,
   parameter   FLASH_ADDR_WIDTH     = 28,
   parameter   FIFO_DEPTH_LOG2      = 9,
   parameter   USE_MEMORY_BLOCKS    = 1
)(
   input  logic                        clk,
   input  logic                        reset,

   //CSR interface
   input  logic                        write_mode,
   input  logic                        read_mode,
   input  logic                        rsu_mode,
   output logic                        flash_busy ,
   output logic [FIFO_DEPTH_LOG2:0]    fifo_dcount,
   input  logic [FIFO_DEPTH_LOG2:0]    read_count,
   input  logic [FLASH_ADDR_WIDTH-1:0] flash_addr,

   //AVMM slave 
   input  logic [7:0]                  avmm_slv_addr,
   input  logic                        avmm_slv_write,
   input  logic                        avmm_slv_read,
   input  logic [31:0]                 avmm_slv_wrdata,
   input  logic [3:0]                  avmm_slv_byteen,
   output logic [31:0]                 avmm_slv_rddata,
   output logic                        avmm_slv_rddvld,
   output logic                        avmm_slv_waitreq,
   
   //AVMM master to flash
   output logic [FLASH_ADDR_WIDTH-1:0] avmm_mstr_addr,
   output logic                        avmm_mstr_write,
   output logic                        avmm_mstr_read,
   output logic [6:0]                  avmm_mstr_burstcnt,
   output logic [31:0]                 avmm_mstr_wrdata,
   input  logic [31:0]                 avmm_mstr_rddata,
   input  logic                        avmm_mstr_rddvld,
   input  logic                        avmm_mstr_waitreq
);

localparam FIFO_DEPTH         = 2**FIFO_DEPTH_LOG2;
localparam RST_DEPTH          = 2;
localparam EN_DBG_STS         = 1; //1 = enable, 0 = disable debug status

//------------------------------------------------------------------------------
// Internal Declarations
//------------------------------------------------------------------------------
enum {
   FBM_RESET_BIT        = 0,
   FBM_READY_BIT        = 1,
   FBM_WR_WAIT_BIT      = 2,
   FBM_WR_REQ_BIT       = 3,
   FBM_RD_REQ_BIT       = 4,
   FBM_RD_DATA_BIT      = 5,
   FBM_DUMMY_RD_BIT     = 6
   
} fbm_state_bit;

enum logic [6:0] {
   FBM_RESET_ST         = 7'h1 << FBM_RESET_BIT   ,
   FBM_READY_ST         = 7'h1 << FBM_READY_BIT   ,
   FBM_WR_WAIT_ST       = 7'h1 << FBM_WR_WAIT_BIT ,
   FBM_WR_REQ_ST        = 7'h1 << FBM_WR_REQ_BIT  ,
   FBM_RD_REQ_ST        = 7'h1 << FBM_RD_REQ_BIT  ,
   FBM_RD_DATA_ST       = 7'h1 << FBM_RD_DATA_BIT ,
   FBM_DUMMY_RD_ST      = 7'h1 << FBM_DUMMY_RD_BIT
} fbm_state, fbm_next;

logic [RST_DEPTH:0]           fifo_reset_cntr;
logic                         fifo_reset;
logic                         write_mode_r1;
logic                         read_mode_r1;
logic                         rsu_mode_r1;
logic                         lsw_rd;
logic [1:0]                   lsw_rd_sr;
logic [31:0]                  fifo_wr_data;
logic                         fifo_wr_req;
logic                         fifo_full;
logic                         fifo_empty;
logic [FIFO_DEPTH_LOG2-1:0]   fifo_usedw;
logic                         fifo_rdreq;
logic [31:0]                  fifo_rddata;
logic [FIFO_DEPTH_LOG2:0]     rd_cntr;
logic [6:0]                   beat_cntr;
logic                         fbm_fifo_rd;
logic                         rd_complete;
logic                         first_beat;
logic [31:0]                  fbm_dbg_sts;

//------------------------------------------------------------------------------
// FBM controls generation
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : fbm_ctrl_seq
   if(reset) begin
      fifo_reset_cntr   <= {RST_DEPTH+1{1'b0}};
      write_mode_r1     <= 1'b0;
      read_mode_r1      <= 1'b0;
      rsu_mode_r1       <= 1'b0;
      fifo_dcount       <= '0;
      flash_busy        <= 1'b0;
   end else begin
      write_mode_r1     <= write_mode;
      read_mode_r1      <= read_mode;
      rsu_mode_r1       <= rsu_mode;
      
      if(!read_mode_r1 && read_mode && !rsu_mode ||
                     !rsu_mode_r1 && rsu_mode || !write_mode_r1 && write_mode)
         fifo_reset_cntr   <= {RST_DEPTH+1{1'b0}};
      else if(!fifo_reset_cntr[RST_DEPTH])
         fifo_reset_cntr   <= fifo_reset_cntr + 1'b1;
         
      flash_busy        <= ~fbm_state[FBM_RESET_BIT] & ~fbm_state[FBM_READY_BIT];
      
      if(fifo_full)
         fifo_dcount    <= '0;
      else
         fifo_dcount    <= FIFO_DEPTH - fifo_usedw;
   end
end : fbm_ctrl_seq

assign fifo_reset = ~fifo_reset_cntr[RST_DEPTH];


//------------------------------------------------------------------------------
// FIFO write logic
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : fifo_wr_seq
   if(reset) begin
      fifo_wr_data      <= 32'h0;
      fifo_wr_req       <= 1'b0;
   end else begin
      if(read_mode_r1)
         fifo_wr_data   <= avmm_mstr_rddata;
      else
         fifo_wr_data   <= avmm_slv_wrdata;
      
      if(read_mode_r1 && avmm_mstr_rddvld || (write_mode_r1 || rsu_mode_r1) && 
                              !fifo_full && avmm_slv_write && !avmm_slv_waitreq)
         fifo_wr_req    <= 1'b1;
      else
         fifo_wr_req    <= 1'b0;
   end
end : fifo_wr_seq

//------------------------------------------------------------------------------
// FIFO read logic
//------------------------------------------------------------------------------
always_comb
begin : fifo_rd_comb
   if(read_mode_r1 && !fifo_empty && avmm_slv_read && !avmm_slv_waitreq)
      lsw_rd = (EN_DBG_STS == 1 && avmm_slv_addr[7]) ? 1'b0 : 1'b1;
   else 
      lsw_rd = 1'b0;
end : fifo_rd_comb

always_ff @(posedge clk, posedge reset)
begin : fifo_rd_seq
   if(reset) begin
      lsw_rd_sr         <= 2'd0;
      fifo_rdreq        <= 1'b0;
      avmm_slv_waitreq  <= 1'b1;
      avmm_slv_rddvld   <= 1'b0;
      avmm_slv_rddata   <= 64'd0;
   end else begin
      lsw_rd_sr         <= {lsw_rd_sr[0], lsw_rd};
      
      if(fbm_fifo_rd || lsw_rd)
         fifo_rdreq     <= 1'b1; 
      else  
         fifo_rdreq     <= 1'b0; 
      
      if((avmm_slv_read || avmm_slv_write) && !avmm_slv_waitreq)
         avmm_slv_waitreq  <= 1'b1;
      else if(lsw_rd_sr == 2'd0)
         avmm_slv_waitreq  <= 1'b0;
         
      if(lsw_rd_sr[1] || avmm_slv_read && !avmm_slv_waitreq && !lsw_rd)
         avmm_slv_rddvld   <= 1'b1;
      else
         avmm_slv_rddvld   <= 1'b0;
      
      if(lsw_rd_sr[1])
         avmm_slv_rddata   <= fifo_rddata;
      else
         avmm_slv_rddata   <= (EN_DBG_STS == 1 && avmm_slv_addr[7]) ? fbm_dbg_sts : 32'h_DEADBEEF;
   end
end : fifo_rd_seq

assign avmm_mstr_wrdata  = fifo_rddata;

//------------------------------------------------------------------------------
// FIFO for storing flash write and read data
//------------------------------------------------------------------------------
scfifo #(
// .intended_device_family(`FAMILY),
   .lpm_numwords           (FIFO_DEPTH),
   .lpm_showahead          ("OFF"),
   .lpm_type               ("scfifo"),
   .lpm_width              (32),
   .lpm_widthu             (9),
   .almost_full_value      (511),
   .overflow_checking      ("ON"),
   .underflow_checking     ("ON"),
   .use_eab                ("ON"),
   .add_ram_output_register("OFF")
) fbm_scfifo (
   .clock         (clk           ),
   .sclr          (fifo_reset    ),

   .data          (fifo_wr_data  ),
   .wrreq         (fifo_wr_req   ),
   .full          (fifo_full     ),
   .almost_full   (),
   .usedw         (fifo_usedw    ),

   .rdreq         (fifo_rdreq    ),
   .q             (fifo_rddata   ),
   .empty         (fifo_empty    ),
   .almost_empty  (),

   .aclr          (),
   .eccstatus     ()
);

//------------------------------------------------------------------------------
// Flash burst master's FSM 
// Top "always_ff" simply switches the state of the state machine registers.
// Following "always_comb" contains all of the next-state decoding logic.
//------------------------------------------------------------------------------
always_ff @(posedge clk)
begin : fbm_sm_seq
   if (fifo_reset)
      fbm_state <= FBM_RESET_ST;
   else
      fbm_state <= fbm_next;
end : fbm_sm_seq

always_comb
begin : fbm_sm_comb
   fbm_next = fbm_state;
   unique case (1'b1) //Reverse Case Statement
      fbm_state[FBM_RESET_BIT]:   //FBM_RESET_ST
         if (fifo_reset)
            fbm_next = FBM_RESET_ST;
         else
            fbm_next = FBM_READY_ST;
      
      fbm_state[FBM_READY_BIT]:   //FBM_READY_ST
         if(rsu_mode_r1 || write_mode_r1)
            fbm_next = FBM_WR_WAIT_ST;
         else if(read_mode_r1 && !rd_complete)
            fbm_next = FBM_RD_REQ_ST;
      
      fbm_state[FBM_WR_WAIT_BIT]: //FBM_WR_WAIT_ST
         if(!(rsu_mode_r1 || write_mode_r1) && fifo_empty)
            fbm_next = FBM_DUMMY_RD_ST;
         else if(!(rsu_mode_r1 || write_mode_r1) && !fifo_empty || 
                                             fifo_full || (fifo_usedw >= 7'd64))
            fbm_next = FBM_WR_REQ_ST;

      fbm_state[FBM_WR_REQ_BIT]: //FBM_WR_REQ_ST
         if(beat_cntr == 7'd0)
            fbm_next = FBM_WR_WAIT_ST;

      fbm_state[FBM_RD_REQ_BIT]: //FBM_RD_REQ_ST
         if(rd_complete)
            fbm_next = FBM_READY_ST;
         else
            fbm_next = FBM_RD_DATA_ST;
      
      fbm_state[FBM_RD_DATA_BIT]: //FBM_RD_DATA_ST
         if(beat_cntr == 7'd0)
            fbm_next = FBM_RD_REQ_ST;
      
      fbm_state[FBM_DUMMY_RD_BIT]: //FBM_DUMMY_RD_ST
         if(avmm_mstr_rddvld)
            fbm_next = FBM_READY_ST;
   endcase
end : fbm_sm_comb

//------------------------------------------------------------------------------
// AvMM master interface (towards flash controller) signal generation
//------------------------------------------------------------------------------
always_ff @(posedge clk)
begin : fsm_ctrl_seq
   if(fbm_state[FBM_READY_BIT] && rsu_mode_r1)
      avmm_mstr_addr <= STAGING_AREA_BADDR;
   else if(fbm_state[FBM_READY_BIT])
      avmm_mstr_addr <= {flash_addr[FLASH_ADDR_WIDTH-1:2], 2'd0};
   else if ((fbm_state[FBM_WR_REQ_BIT] || fbm_state[FBM_RD_DATA_BIT]) && 
                                                            (beat_cntr == 7'd0))
      avmm_mstr_addr <= avmm_mstr_addr + 9'd256;

   if (fbm_state[FBM_WR_WAIT_BIT])
      first_beat <= 1'b1;
   else
      first_beat <= 1'b0;
   
   if(fifo_reset)
      avmm_mstr_write   <= 1'b0;
   else if(fbm_state[FBM_WR_REQ_BIT] && fifo_rdreq)
      avmm_mstr_write   <= 1'b1;
   else if(!fbm_state[FBM_WR_REQ_BIT] || !avmm_mstr_waitreq)
      avmm_mstr_write   <= 1'b0;
   
   if(fifo_reset)
      avmm_mstr_read    <= 1'b0;
   else if((fbm_state[FBM_RD_REQ_BIT] || fbm_state[FBM_DUMMY_RD_BIT]) && !rd_complete)
      avmm_mstr_read    <= 1'b1;
   else if(!avmm_mstr_waitreq)   
      avmm_mstr_read    <= 1'b0;
   
   if(fbm_state[FBM_READY_BIT])
      rd_cntr    <= read_count;
   else if(fbm_state[FBM_RD_REQ_BIT] && rd_cntr >= 7'd64)   
      rd_cntr    <= rd_cntr - 7'd64;
   else if(fbm_state[FBM_RD_REQ_BIT])   
      rd_cntr    <= '0;
   
   if (fbm_state[FBM_WR_WAIT_BIT] && (fifo_usedw >= 7'd64 || fifo_full) || 
       fbm_state[FBM_RD_REQ_BIT]  && rd_cntr >= 7'd64)
      beat_cntr <= 7'd64;
   else if(fbm_state[FBM_WR_WAIT_BIT])
      beat_cntr <= fifo_usedw[6:0];
   else if(fbm_state[FBM_RD_REQ_BIT])
      beat_cntr <= rd_cntr[6:0];
   else if(fbm_state[FBM_DUMMY_RD_BIT])
      beat_cntr <= 7'd1;
   else if(fbm_state[FBM_WR_REQ_BIT] && avmm_mstr_write && !avmm_mstr_waitreq || 
           fbm_state[FBM_RD_DATA_BIT] && avmm_mstr_rddvld)
      beat_cntr <= beat_cntr - 1'b1;
      
   if(fbm_state[FBM_RESET_BIT])
      rd_complete <= 1'b0;
   else if(fbm_state[FBM_RD_DATA_BIT] && (rd_cntr == {(FIFO_DEPTH_LOG2+1){1'b0}}) || 
                                                     fbm_state[FBM_DUMMY_RD_BIT])
      rd_complete <= 1'b1;
end : fsm_ctrl_seq

always_comb
begin : fsm_ctrl_comb   
   if (fbm_state[FBM_WR_REQ_BIT] && (first_beat || 
               avmm_mstr_write && !avmm_mstr_waitreq && beat_cntr[6:1] != 6'd0))
      fbm_fifo_rd = 1'b1;
   else
      fbm_fifo_rd = 1'b0;
end : fsm_ctrl_comb

assign avmm_mstr_burstcnt = beat_cntr;


//------------------------------------------------------------------------------
// FBM's Debug status
//------------------------------------------------------------------------------
always_comb
begin : dbg_sts_seq
   fbm_dbg_sts = {8'd0, //[31:24]
                 1'b0, write_mode_r1, read_mode_r1, rsu_mode_r1, //[23:20]
                 rd_complete, avmm_mstr_waitreq, avmm_mstr_write, avmm_mstr_read, //[19:16]
                 1'b0, beat_cntr,  //[15:8]
                 1'b0, fbm_state}; //[7:0]


end : dbg_sts_seq

endmodule
