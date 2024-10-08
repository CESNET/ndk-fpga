// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// This SPI master converts Avalon-MM to SPI transactions which are compatible
// with 'SPI Slave to Avalon Master Bridge Core' from Quartus Platform Designer.
// This SPI master has two Avalon-MM slave interfaces through which it receives 
// commands from the master. One of them implements a mailbox register for 
// indirect access of CSR registers from SPI slave and other implements direct 
// bridge between burst capable Avalon-MM to SPI. 
// Host system can use this IP paired with 'SPI Slave to Avalon Master Bridge 
// Core' to access slave's memory mapped registers.
//-----------------------------------------------------------------------------

module avmms_2_spim_bridge #(
   parameter   CSR_DATA_WIDTH    = 64,
   parameter   DIR_BASE_ADDR     = 32'h0001_0000,
   parameter   DIR_ADDR_WIDTH    = 9,
   parameter   DIR_BRST_WIDTH    = 9,
   parameter   USE_MEMORY_BLOCKS = 1,
   parameter   SCLK_CLK_DIV      = 0,  //SCLK clock frequency = input_clock_frequeny / ((SCLK_CLK_DIV+1)*2)
   parameter   MISO_CAPT_DLY     = 1,  //MISO capture delay in terms of ref clock cycles (0 = no delay)
   parameter   CSR_ADDR_WIDTH    = 2,  //2 for 64bit data and 3 for 32bit data
   parameter   SLV_CSR_AWIDTH    = 16, //Should be less than DIR_BASE_ADDR. Lower range is used
                                       //for CSR based and higher range for direct.
   parameter   SPI_DEBUG_EN      = 1
)(
   input  logic                        clk,
   input  logic                        reset,

   input  logic [CSR_ADDR_WIDTH-1:0]   avmm_csr_addr,
   input  logic                        avmm_csr_write,
   input  logic                        avmm_csr_read,
   input  logic [(CSR_DATA_WIDTH/8)-1:0]    avmm_csr_byteen,
   input  logic [CSR_DATA_WIDTH-1:0]   avmm_csr_wrdata,
   output logic [CSR_DATA_WIDTH-1:0]   avmm_csr_rddata,
   output logic                        avmm_csr_rddvld,
   output logic                        avmm_csr_waitreq,
   
   input  logic [DIR_ADDR_WIDTH-1:0]   avmm_dir_addr,
   input  logic                        avmm_dir_write,
   input  logic                        avmm_dir_read,
   input  logic [DIR_BRST_WIDTH-1:0]   avmm_dir_burstcnt,
   input  logic [31:0]                 avmm_dir_wrdata,
   output logic [31:0]                 avmm_dir_rddata,
   output logic                        avmm_dir_rddvld,
   output logic                        avmm_dir_waitreq,

   output logic                        spim_clk,
   output logic                        spim_csn,
   input  logic                        spim_miso,
   output logic                        spim_mosi
);

localparam FIFO_DEPTH         = 2**(DIR_BRST_WIDTH-1);
localparam CLK_DIV_WIDTH      = (SCLK_CLK_DIV < 4) ? 2 : $clog2(SCLK_CLK_DIV+1);
localparam MISO_DLY_WIDTH     = (MISO_CAPT_DLY < 2) ? 1 : $clog2(MISO_CAPT_DLY+1);
localparam DBG_WR_TIMEOUT     = 8'd80;
localparam DBG_RD_TIMEOUT     = 8'd160;

//------------------------------------------------------------------------------
// Internal Declarations
//------------------------------------------------------------------------------
enum {
   SPIM_RESET_BIT        = 0,
   SPIM_READY_BIT        = 1,
   SPIM_START_BIT        = 2,
   SPIM_CMD_BIT          = 3,
   SPIM_ADDR_BIT         = 4,
   SPIM_WRDATA_BIT       = 5,
   SPIM_RDFIFO_BIT       = 6,
   SPIM_WRRESP_BIT       = 7,
   SPIM_RDDATA_BIT       = 8,
   SPIM_COMPLETE_BIT     = 9
} spim_state_bit;

enum logic [9:0] {
   SPIM_RESET_ST         = 10'h1 << SPIM_RESET_BIT   ,
   SPIM_READY_ST         = 10'h1 << SPIM_READY_BIT   ,
   SPIM_START_ST         = 10'h1 << SPIM_START_BIT   ,
   SPIM_CMD_ST           = 10'h1 << SPIM_CMD_BIT     ,
   SPIM_ADDR_ST          = 10'h1 << SPIM_ADDR_BIT    ,
   SPIM_WRDATA_ST        = 10'h1 << SPIM_WRDATA_BIT  ,
   SPIM_RDFIFO_ST        = 10'h1 << SPIM_RDFIFO_BIT  ,
   SPIM_WRRESP_ST        = 10'h1 << SPIM_WRRESP_BIT  ,
   SPIM_RDDATA_ST        = 10'h1 << SPIM_RDDATA_BIT  ,
   SPIM_COMPLETE_ST      = 10'h1 << SPIM_COMPLETE_BIT
} spim_state, spim_next;

logic [2:0]                cmd_reg;
logic [SLV_CSR_AWIDTH-1:0] addr_reg;  
logic [31:0]               wrdata_reg;
logic [31:0]               rddata_reg;
logic [31:0]               ctrl_reg;  
logic [31:0]               ctrl_reg_rd;  
logic [31:0]               sts0_reg_rd;  
logic [31:0]               sts1_reg_rd;  
logic [31:0]               sts2_reg_rd;  
logic                      ack_trans;      
logic                      first_beat;      
logic                      read_latch;      
logic                      fifo_in_sop;
logic                      fifo_in_eop;
logic                      fifo_in_valid;
logic [31:0]               fifo_in_data;
logic                      fifo_in_ready;
logic [31:0]               fifo_out_data ;
logic                      fifo_out_valid;
logic                      fifo_out_ready;
logic                      fifo_out_sop  ;
logic                      fifo_out_eop  ;
logic [DIR_BRST_WIDTH-1:0] burst_beat;
logic [DIR_BRST_WIDTH-1:0] brst_cnt_latch;
logic [DIR_ADDR_WIDTH-1:0] addr_latch;
logic                      csr_cmd;
logic                      rd_cmd;
logic [DIR_BRST_WIDTH+1:0] byte_cntr;
logic                      resp_sop_rcvd;
logic [1:0]                resp_chk_cntr;
logic                      no_response;
logic                      spi_error;
logic                      p2b_in_valid;
logic                      p2b_in_ready;
logic                      p2b_in_sop;
logic                      p2b_in_eop;
logic [7:0]                p2b_in_data;
logic                      b2p_out_valid;
logic                      b2p_out_ready;
logic                      b2p_out_sop;
logic                      b2p_out_eop;
logic [7:0]                b2p_out_data;
logic [7:0]                dbg_txn_error;
logic [7:0]                dbg_wrd_pndng;
logic                      dbg_fifo_read;
logic [31:0]               cmd_mux;
logic [DIR_BRST_WIDTH+1:0] size_mux;
logic [15:0]               dbg_size_mux;
logic                      time_out;
logic [7:0]                to_cntr;
logic [9:0]                dbg_to_state;
logic [31:0]               dbg_wrresp;
logic [7:0]                dbg_wrresp_pkt;
logic                      p2b_out_ready;
logic                      p2b_out_valid;
logic [7:0]                p2b_out_data;
logic                      b2p_in_ready;
logic                      b2p_in_valid;
logic [7:0]                b2p_in_data;
logic                      stop_spi;
logic [CLK_DIV_WIDTH-1:0]  clk_cntr;
logic                      spim_clk_r1;
logic                      first_sclk;
logic                      clk_pedge;
logic [MISO_CAPT_DLY:0]    clk_nedge;
logic                      miso_byte_en;
logic                      miso_cptr_nedge;
logic [7:0]                mosi_shift_reg;
logic [2:0]                mosi_bit_cntr;
logic [7:0]                mosi_data_byte;
logic                      esc_sent;
logic                      tx_end_n;
logic [3:0]                spi_pause_cntr;
logic [2:0]                miso_bit_cntr;
logic [7:0]                miso_data_byte;
logic                      esc_rcvd;

//------------------------------------------------------------------------------
// Function to update CSR register
//------------------------------------------------------------------------------
function automatic logic[31:0] csr_reg_write (
   input logic          [2:0]                      reg_addr,
   input logic          [31:0]                     reg_cur_data,
   input logic          [CSR_ADDR_WIDTH-1:0]       csr_addr,
   input logic          [CSR_DATA_WIDTH-1:0]       csr_data,
   input logic          [(CSR_DATA_WIDTH/8)-1:0]   csr_ben
);
   if (CSR_DATA_WIDTH == 32) begin
      csr_reg_write = (csr_addr == reg_addr && csr_ben == 4'hF) ? csr_data : reg_cur_data;
   end else begin
      if (reg_addr[0])
         csr_reg_write = (csr_addr == reg_addr[2:1] && csr_ben[7:4] == 4'hF) ? csr_data[63:32]: reg_cur_data  ;
      else 
         csr_reg_write = (csr_addr == reg_addr[2:1] && csr_ben[3:0] == 4'hF) ? csr_data[31:0] : reg_cur_data  ;
   end
   return csr_reg_write;
endfunction

//------------------------------------------------------------------------------
// CSR write decode logic
//
//1. Write desired data into the Write Data register, offset 0xc.
//2. Write desired address to the Address Register, offset 0x4
//3. Write 0x2 to the Command/Status register, offset 0x0.
//4. Poll Command/Status register, offset 0x0, until ACK_TRANS bit gets set to 1
//5. Write 0x0 to Command/Status register, offset 0x0.
//
//1. Write desired address to the Address Register, offset 0x4.
//2. Write 0x1 to the Command/Status register, offset 0x0.
//3. Poll Command/Status register, offset 0x0, until ACK_TRANS bit gets set to 1
//4. Read the data from the Read Data register, offset 0x8.
//5. Write 0x0 to Command/Status register, offset 0x0.
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : csr_wr
   if(reset) begin
      cmd_reg     <= 3'd0;
      addr_reg    <= {SLV_CSR_AWIDTH{1'b0}};
      wrdata_reg  <= 32'd0;
   end else if (avmm_csr_write && !avmm_csr_waitreq) begin
      cmd_reg     <= csr_reg_write(3'h0, {29'd0, cmd_reg}, avmm_csr_addr, avmm_csr_wrdata, avmm_csr_byteen);
      addr_reg    <= csr_reg_write(3'h1, {{(32-SLV_CSR_AWIDTH){1'b0}}, addr_reg}, avmm_csr_addr, avmm_csr_wrdata, avmm_csr_byteen);
      wrdata_reg  <= csr_reg_write(3'h3, wrdata_reg, avmm_csr_addr, avmm_csr_wrdata, avmm_csr_byteen);
   end else if (ack_trans) begin
      cmd_reg[2]  <= 1'b1;
   end
end : csr_wr


//------------------------------------------------------------------------------
// Debug register - write and read
//------------------------------------------------------------------------------
generate
if (SPI_DEBUG_EN == 1)
begin
   
   always_ff @(posedge clk, posedge reset)
   begin : ctrl_reg_wr
      if(reset) begin
         ctrl_reg[31:16] <= 16'd0;
         ctrl_reg[15:8]  <= MISO_CAPT_DLY;
         ctrl_reg[7:0]   <= SCLK_CLK_DIV;
      end else if (avmm_csr_write && !avmm_csr_waitreq) begin
       //ctrl_reg    <= (avmm_csr_addr == 3'h4 && avmm_csr_byteen == 4'hF) ? avmm_csr_wrdata : ctrl_reg  ;
         ctrl_reg    <= csr_reg_write(3'h4, ctrl_reg, avmm_csr_addr, avmm_csr_wrdata, avmm_csr_byteen);
      end
   end : ctrl_reg_wr
   
   always_comb 
   begin : dbg_en_rd_comb
      ctrl_reg_rd = {16'd0, ctrl_reg[15:0]};
      sts0_reg_rd = {6'd0, dbg_to_state, dbg_wrd_pndng, dbg_txn_error};
      sts1_reg_rd = {8'd0, dbg_wrresp_pkt, 6'd0, spim_state};
      sts2_reg_rd = dbg_wrresp;
   end : dbg_en_rd_comb 
   
end else begin //SPI_DEBUG_EN == 0
   
   always_comb 
   begin : dbg_dis_rd_comb
      ctrl_reg[31:16] = 16'd0;
      ctrl_reg[15:8]  = MISO_CAPT_DLY;
      ctrl_reg[7:0]   = SCLK_CLK_DIV;
      ctrl_reg_rd     = 32'hDEADBEEF;
      sts0_reg_rd     = 32'hDEADBEEF;
      sts1_reg_rd     = 32'hDEADBEEF;
      sts2_reg_rd     = 32'hDEADBEEF;
   end : dbg_dis_rd_comb 
   
end
endgenerate


//------------------------------------------------------------------------------
// CSR read decode logic
//------------------------------------------------------------------------------
generate
if (CSR_DATA_WIDTH == 32) begin
   always_ff @(posedge clk, posedge reset)
   begin : csr_rd
      if(reset) begin
         avmm_csr_rddata <= 32'd0;
         avmm_csr_rddvld <= 1'b0;
      end else if (avmm_csr_read && !avmm_csr_waitreq) begin
         avmm_csr_rddvld <= 1'b1;
         case (avmm_csr_addr)
            3'h0    : avmm_csr_rddata <= {spi_error, 28'd0 , cmd_reg};
            3'h1    : avmm_csr_rddata <= {{(32-SLV_CSR_AWIDTH){1'b0}}, addr_reg};
            3'h2    : avmm_csr_rddata <= rddata_reg;
            3'h3    : avmm_csr_rddata <= wrdata_reg;
            3'h4    : avmm_csr_rddata <= ctrl_reg_rd;
            3'h5    : avmm_csr_rddata <= sts0_reg_rd;
            3'h6    : avmm_csr_rddata <= sts1_reg_rd;
            3'h7    : avmm_csr_rddata <= sts2_reg_rd;
            default : avmm_csr_rddata <= 32'hDEADBEEF;
         endcase
      end else begin
         avmm_csr_rddvld <= 1'b0;
      end
   end : csr_rd
end else begin //CSR_DATA_WIDTH == 64
   always_ff @(posedge clk, posedge reset)
   begin : csr_rd
      if(reset) begin
         avmm_csr_rddata <= 64'd0;
         avmm_csr_rddvld <= 1'b0;
      end else if (avmm_csr_read && !avmm_csr_waitreq) begin
         avmm_csr_rddvld <= 1'b1;
         case (avmm_csr_addr)
            2'h0    : avmm_csr_rddata <= {{{(32-SLV_CSR_AWIDTH){1'b0}}, addr_reg}, 
                                          spi_error, 28'd0 , cmd_reg};
            2'h1    : avmm_csr_rddata <= {wrdata_reg, rddata_reg};
            2'h2    : avmm_csr_rddata <= {sts0_reg_rd, ctrl_reg_rd};
            2'h3    : avmm_csr_rddata <= {sts2_reg_rd, sts1_reg_rd};
            default : avmm_csr_rddata <= 64'hDEADBEEF_DEADBEEF;
         endcase
      end else begin
         avmm_csr_rddvld <= 1'b0;
      end
   end : csr_rd
end
endgenerate

//------------------------------------------------------------------------------
// AVMM slave waitreq generation
//------------------------------------------------------------------------------
assign avmm_csr_waitreq = spim_state[SPIM_RESET_BIT];
assign avmm_dir_waitreq = spim_state[SPIM_RESET_BIT] | fifo_in_eop | read_latch;

//------------------------------------------------------------------------------
// FIFO write logic
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : fifo_wr
   if(reset) begin
      first_beat        <= 1'b1;
      fifo_in_sop       <= 1'b0;
      fifo_in_eop       <= 1'b0;
      read_latch        <= 1'b0;
      fifo_in_valid     <= 1'b0;
      fifo_in_data      <= 32'h0;
      burst_beat        <= 'h0;
      addr_latch        <= 'h0;
      brst_cnt_latch    <= 'h0;
   end else begin
      if(fifo_in_eop | read_latch)
         first_beat     <= 1'b1;
      else if((avmm_dir_write || avmm_dir_read) && !avmm_dir_waitreq)
         first_beat     <= 1'b0;
      
      fifo_in_sop       <= first_beat;
      
      //use fifo_in_eop as write in progress indication
      if((first_beat && avmm_dir_burstcnt == 'h1 || burst_beat == 2'h2) && 
                                            !avmm_dir_waitreq && avmm_dir_write)
         fifo_in_eop    <= 1'b1;
      else if(fifo_out_eop && fifo_out_valid && fifo_out_ready)
         fifo_in_eop    <= 1'b0;
      
      //latch read for FSM capture
      if(!avmm_dir_waitreq && avmm_dir_read)
         read_latch     <= 1'b1;
      else if(spim_state[SPIM_COMPLETE_BIT] && !csr_cmd && rd_cmd)
         read_latch     <= 1'b0;
      
      fifo_in_valid     <= ~avmm_dir_waitreq & avmm_dir_write;
      fifo_in_data      <= avmm_dir_wrdata;
      
      if(first_beat && avmm_dir_write && !avmm_dir_waitreq)
         burst_beat     <= avmm_dir_burstcnt;
      else if(!avmm_dir_waitreq && avmm_dir_write)
         burst_beat     <= burst_beat - 1'b1;
         
      if(first_beat && !avmm_dir_waitreq) begin
         addr_latch     <= avmm_dir_addr;
         brst_cnt_latch <= avmm_dir_burstcnt;
      end
   end
end : fifo_wr

//------------------------------------------------------------------------------
// FIFO for storing AVMM bursts
//------------------------------------------------------------------------------
spi_sc_fifo #(
   .SYMBOLS_PER_BEAT    (1                ),
   .BITS_PER_SYMBOL     (32               ),
   .FIFO_DEPTH          (FIFO_DEPTH       ),
   .CHANNEL_WIDTH       (0                ),
   .ERROR_WIDTH         (0                ),
   .USE_PACKETS         (1                ),
   .USE_FILL_LEVEL      (0                ),
   .EMPTY_LATENCY       (3                ),
   .USE_MEMORY_BLOCKS   (USE_MEMORY_BLOCKS),
   .USE_STORE_FORWARD   (0                ),
   .USE_ALMOST_FULL_IF  (0                ),
   .USE_ALMOST_EMPTY_IF (0                )
) avst_fifo (
   .clk                 (clk              ),
   .reset               (reset            ),
   .in_data             (fifo_in_data     ),
   .in_valid            (fifo_in_valid    ),
   .in_ready            (                 ), //(fifo_in_ready    ),
   .in_startofpacket    (fifo_in_sop      ),
   .in_endofpacket      (fifo_in_eop      ),
   .out_data            (fifo_out_data    ),
   .out_valid           (fifo_out_valid   ),
   .out_ready           (fifo_out_ready   ),
   .out_startofpacket   (fifo_out_sop     ),
   .out_endofpacket     (fifo_out_eop     )
);

//------------------------------------------------------------------------------
// SPI-Master packetizer FSM 
// Top "always_ff" simply switches the state of the state machine registers.
// Following "always_comb" contains all of the next-state decoding logic.
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : spim_fsm_seq
   if (reset)
      spim_state <= SPIM_RESET_ST;
   else
      spim_state <= spim_next;
end : spim_fsm_seq

always_comb
begin : spim_fsm_comb
   spim_next = spim_state;
   unique case (1'b1) //Reverse Case Statement
      spim_state[SPIM_RESET_BIT]:   //SPIM_RESET_ST
         if (reset)
            spim_next = SPIM_RESET_ST;
         else
            spim_next = SPIM_READY_ST;
      
      spim_state[SPIM_READY_BIT]:   //SPIM_READY_ST
         if((!cmd_reg[2] && cmd_reg[1:0] != 2'd0) || fifo_in_eop || read_latch)
            spim_next = SPIM_START_ST;
      
      spim_state[SPIM_START_BIT]: //SPIM_START_ST
         spim_next = SPIM_CMD_ST;
      
      spim_state[SPIM_CMD_BIT]:   //SPIM_CMD_ST
         if (time_out)
            spim_next = SPIM_COMPLETE_ST;
         else if(byte_cntr == 'h0)
            spim_next = SPIM_ADDR_ST;
      
      spim_state[SPIM_ADDR_BIT]:    //SPIM_ADDR_ST
         if (time_out)
            spim_next = SPIM_COMPLETE_ST;
         else if(byte_cntr == 'h0 && rd_cmd)
            spim_next = SPIM_RDDATA_ST;
         else if(byte_cntr == 'h0)
            spim_next = SPIM_WRDATA_ST;
      
      spim_state[SPIM_WRDATA_BIT]:  //SPIM_WRDATA_ST
         if (time_out)
            spim_next = SPIM_COMPLETE_ST;
         else if(byte_cntr == 'h1 && p2b_in_valid && p2b_in_ready)
            spim_next = SPIM_WRRESP_ST;
         else if(byte_cntr[1:0] == 2'd1 && p2b_in_valid && p2b_in_ready)
            spim_next = SPIM_RDFIFO_ST;
      
      spim_state[SPIM_RDFIFO_BIT]:  //SPIM_RDFIFO_ST
         spim_next = SPIM_WRDATA_ST;

      spim_state[SPIM_WRRESP_BIT]:  //SPIM_WRRESP_ST
         if(no_response || time_out || byte_cntr == 'h0)
            spim_next = SPIM_COMPLETE_ST;

      spim_state[SPIM_RDDATA_BIT]:  //SPIM_RDDATA_ST
         if(no_response || time_out || byte_cntr == 'h0)
            spim_next = SPIM_COMPLETE_ST;

      spim_state[SPIM_COMPLETE_BIT]://SPIM_COMPLETE_ST
         if(!dbg_fifo_read)
            spim_next    = SPIM_READY_ST;
   endcase
end : spim_fsm_comb

      
//------------------------------------------------------------------------------
// FSM control generation logic
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : fsm_ctrl_seq
   if(reset) begin
      csr_cmd        <= 1'b0;
      rd_cmd         <= 1'b0;
      cmd_mux        <= 32'd0;
      size_mux       <= 'd0;
      byte_cntr      <= 'h0;
      resp_sop_rcvd  <= 1'b0;
      resp_chk_cntr  <= 2'd0;
      no_response    <= 1'b0;
      spi_error      <= 1'b0;
   end else begin
      //Read/write and CSR/direct differentiation
      if (spim_state[SPIM_READY_BIT]) begin
         csr_cmd  <= (!cmd_reg[2] && cmd_reg[1:0] != 2'd0) ? 1'b1 : 1'b0;
         rd_cmd   <= (~cmd_reg[2] & cmd_reg[0]) | ((cmd_reg[2] | ~cmd_reg[1]) & read_latch);
      end
      
      //Address and length of the write/read data 
      if(spim_state[SPIM_START_BIT]) begin
         cmd_mux[31:16] <= rd_cmd  ? 16'h1400 : 16'h0400;
         cmd_mux[15:0]  <= csr_cmd ? 16'h0004 : {{(14-DIR_BRST_WIDTH){1'b0}}, brst_cnt_latch, 2'd0};
         size_mux       <= csr_cmd ? 'h4 : {brst_cnt_latch, 2'd0};
      end else if (spim_state[SPIM_CMD_BIT] && byte_cntr[2:0] == 'h0) begin
         if (csr_cmd)
            cmd_mux     <= {{(32-SLV_CSR_AWIDTH){1'b0}}, addr_reg[SLV_CSR_AWIDTH-1:2], 2'd0};
         else begin
            cmd_mux[31:DIR_ADDR_WIDTH+2] <= DIR_BASE_ADDR >> (DIR_ADDR_WIDTH+2);
            cmd_mux[DIR_ADDR_WIDTH+1:0]  <= {addr_latch, 2'd0};
         end
      end
      
      if(!spim_state[SPIM_WRRESP_BIT] && !spim_state[SPIM_RDDATA_BIT])
         resp_sop_rcvd  <= 1'b0;
      else if(b2p_out_sop)
         resp_sop_rcvd  <= 1'b1;
         
      if(tx_end_n || resp_sop_rcvd)
         resp_chk_cntr  <= 2'd0;
      else if(b2p_out_valid)
         resp_chk_cntr  <= resp_chk_cntr + 1'b1;
         
      if(!spim_state[SPIM_WRRESP_BIT] && !spim_state[SPIM_RDDATA_BIT])
         no_response  <= 1'b0;
      else if(resp_chk_cntr == 2'd3)
         no_response  <= 1'b1;
         
      //Byte counter of the FSM 
      if(spim_state[SPIM_START_BIT]  || 
         spim_state[SPIM_CMD_BIT]    && byte_cntr == 'h0 ||
         spim_state[SPIM_WRDATA_BIT] && p2b_in_valid && p2b_in_ready && byte_cntr == 'h1)
         byte_cntr    <= 'h4;
      else if(spim_state[SPIM_ADDR_BIT] && byte_cntr == 'h0)
         byte_cntr    <= size_mux;
      else if(spim_state[SPIM_CMD_BIT]    && p2b_in_ready  || //&& p2b_in_valid 
              spim_state[SPIM_ADDR_BIT]   && p2b_in_ready  || //&& p2b_in_valid  
              spim_state[SPIM_WRDATA_BIT] && p2b_in_ready  || //&& p2b_in_valid 
              spim_state[SPIM_WRRESP_BIT] && resp_sop_rcvd && b2p_out_valid ||
              spim_state[SPIM_RDDATA_BIT] && resp_sop_rcvd && b2p_out_valid)
         byte_cntr    <= byte_cntr - 1'b1;
         
      //SPI transaction error (only for the Nios/Host interface i.e. for CSR based)
      if(spim_state[SPIM_START_BIT] && csr_cmd)
         spi_error <= 1'b0;
      else if(spim_state[SPIM_CMD_BIT]    && time_out ||
              spim_state[SPIM_ADDR_BIT]   && time_out ||
              spim_state[SPIM_WRDATA_BIT] && time_out ||
              spim_state[SPIM_WRRESP_BIT] && (no_response || time_out) ||
              spim_state[SPIM_RDDATA_BIT] && (no_response || time_out))
         spi_error <= 1'b1;
   end
end : fsm_ctrl_seq

//------------------------------------------------------------------------------
// FSM output generation
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : fsm_out_seq
   if(reset) begin
      p2b_in_valid    <= 1'b0;
      p2b_in_sop      <= 1'b0;
      p2b_in_eop      <= 1'b0;
      p2b_in_data     <= 8'd0;
      fifo_out_ready  <= 1'b0;
      avmm_dir_rddata <= 32'd0;
      rddata_reg      <= 32'd0;
      b2p_out_ready   <= 1'b0;
      avmm_dir_rddvld <= 1'b0; 
   end else begin
      //Start of packet indication to P2B module
      if (spim_state[SPIM_START_BIT])
         p2b_in_sop   <= 1'b1;
      else if(p2b_in_ready)
         p2b_in_sop   <= 1'b0;
      
      //End of packet indication to P2B module
      if(spim_state[SPIM_ADDR_BIT] && byte_cntr == 'h1 && rd_cmd ||
         spim_state[SPIM_WRDATA_BIT] && byte_cntr == 'h1)
         p2b_in_eop   <= 1'b1;
      else
         p2b_in_eop   <= 1'b0;
      
      //Data valid indication to P2B module
      if(p2b_in_ready)
         p2b_in_valid <= 1'b0;
      else if(spim_state[SPIM_CMD_BIT] || spim_state[SPIM_ADDR_BIT] || 
                                                   spim_state[SPIM_WRDATA_BIT])
         p2b_in_valid <= 1'b1;
      else
         p2b_in_valid <= 1'b0;
         
      //Data to P2B module
      if(spim_state[SPIM_CMD_BIT] || spim_state[SPIM_ADDR_BIT])
         unique case (byte_cntr[1:0])
            2'd0 : p2b_in_data  <= cmd_mux[3*8+:8];
            2'd3 : p2b_in_data  <= cmd_mux[2*8+:8];
            2'd2 : p2b_in_data  <= cmd_mux[1*8+:8];
            2'd1 : p2b_in_data  <= cmd_mux[0*8+:8];
         endcase
      else if(spim_state[SPIM_WRDATA_BIT])
         unique case (byte_cntr[1:0])
            2'd0 : p2b_in_data  <= csr_cmd ? wrdata_reg[0*8+:8] : fifo_out_data[0*8+:8];
            2'd3 : p2b_in_data  <= csr_cmd ? wrdata_reg[1*8+:8] : fifo_out_data[1*8+:8];
            2'd2 : p2b_in_data  <= csr_cmd ? wrdata_reg[2*8+:8] : fifo_out_data[2*8+:8];
            2'd1 : p2b_in_data  <= csr_cmd ? wrdata_reg[3*8+:8] : fifo_out_data[3*8+:8];
         endcase
      
      //Pop out data from FIFO
      //if(spim_state[SPIM_RDFIFO_BIT] || dbg_fifo_read)
      if(spim_state[SPIM_WRDATA_BIT] && byte_cntr[1:0] == 2'd1 && !csr_cmd && 
                                  p2b_in_valid && p2b_in_ready || dbg_fifo_read)
         fifo_out_ready <= 1'b1;
      else
         fifo_out_ready <= 1'b0;
      
      //Ready indication to B2P module
      b2p_out_ready <= 1'b1;
         
      //Read response of direct AVMM slave
      if(spim_state[SPIM_RDDATA_BIT] && b2p_out_valid) begin
         avmm_dir_rddata <= {b2p_out_data, avmm_dir_rddata[31:8]};
         avmm_dir_rddvld <= (!csr_cmd && byte_cntr[1:0] == 2'd1) ? 1'b1 : 1'b0;
      end else 
         avmm_dir_rddvld <= 1'b0;
      
      //Read data register of CSR
      if (spim_state[SPIM_COMPLETE_BIT] && csr_cmd) begin
         rddata_reg <= avmm_dir_rddata;
      end
   end
end : fsm_out_seq

always_comb
begin : fsm_out_comb
   ack_trans = spim_state[SPIM_COMPLETE_BIT] & csr_cmd;
end : fsm_out_comb

//------------------------------------------------------------------------------
// Debug - FMS timeout implementation
//------------------------------------------------------------------------------
generate
if (SPI_DEBUG_EN == 1)
begin

   assign dbg_size_mux = {{(14-DIR_BRST_WIDTH){1'b0}}, size_mux};
   
   always_ff @(posedge clk, posedge reset)
   begin : fsm_dbg_seq
      if(reset) begin
         time_out       <= 1'b0;
         to_cntr        <= 8'd0;
         dbg_to_state   <= 10'd0;
         dbg_txn_error  <= 8'd0;
         dbg_wrd_pndng  <= 8'd0;
         dbg_wrresp     <= 32'd0;
         dbg_wrresp_pkt <= 8'd0;
      end else begin
         time_out <= 1'b0;
         //FSM decode
         if(spim_state[SPIM_START_BIT]) begin
            dbg_to_state <= 9'd0;
         end else if (spim_state[SPIM_CMD_BIT] || spim_state[SPIM_ADDR_BIT] ||
                                           spim_state[SPIM_WRDATA_BIT]) begin
            if(p2b_in_ready)
               to_cntr <= 8'd0;
            else if(clk_pedge)
               to_cntr <= to_cntr + 1'b1;
            
            if(to_cntr == DBG_WR_TIMEOUT) begin
               time_out <= 1'b1;
               dbg_to_state <= spim_state;
            end
         end else if(spim_state[SPIM_WRRESP_BIT] || spim_state[SPIM_RDDATA_BIT]) begin
            if(b2p_in_valid)
               to_cntr <= 8'd0;
            else if(clk_pedge)
               to_cntr <= to_cntr + 1'b1;
               
            if(to_cntr == DBG_RD_TIMEOUT) begin
               time_out <= 1'b1;
               dbg_to_state <= spim_state;
            end
         end
         
         //transaction error
         if(spim_state[SPIM_START_BIT]) begin
            dbg_txn_error <= 8'h0;
            dbg_wrresp    <= 32'h0;
            dbg_wrresp_pkt<= 8'h0;
         end else if(spim_state[SPIM_WRRESP_BIT] && b2p_out_valid) begin
            case(byte_cntr[2:0])
               3'd4 : begin
                  dbg_txn_error[4] <= b2p_out_sop ? 1'b0 : 1'b1;
                  dbg_txn_error[3] <= (b2p_out_data != 8'h84) ? 1'b1 : 1'b0;
                  dbg_wrresp[8*3+:8] <= b2p_out_data;
                  dbg_wrresp_pkt[2*3+:2] <= {b2p_out_sop, b2p_out_eop};
               end
               3'd3 : begin
                  dbg_txn_error[2] <= (b2p_out_data != 8'h00) ? 1'b1 : 1'b0;
                  dbg_wrresp[8*2+:8] <= b2p_out_data;
                  dbg_wrresp_pkt[2*2+:2] <= {b2p_out_sop, b2p_out_eop};
               end
               3'd2 : begin
                  dbg_txn_error[1] <= (b2p_out_data != dbg_size_mux[15:8]) ? 1'b1 : 1'b0;
                  dbg_wrresp[8*1+:8] <= b2p_out_data;
                  dbg_wrresp_pkt[2*1+:2] <= {b2p_out_sop, b2p_out_eop};
               end
               3'd1 : begin
                  dbg_txn_error[5] <= b2p_out_eop ? 1'b0 : 1'b1;
                  dbg_txn_error[0] <= (b2p_out_data != dbg_size_mux[7:0])  ? 1'b1 : 1'b0;
                  dbg_wrresp[8*0+:8] <= b2p_out_data;
                  dbg_wrresp_pkt[2*0+:2] <= {b2p_out_sop, b2p_out_eop};
               end
               default : begin
                  dbg_txn_error  <= dbg_txn_error;
                  dbg_wrresp     <= b2p_out_data;
               end
            endcase
         end else if (spim_state[SPIM_RDDATA_BIT] && b2p_out_valid) begin
            dbg_txn_error[6] <= (byte_cntr == size_mux && !b2p_out_sop) ? 1'b1 : 1'b0;
            dbg_txn_error[7] <= (byte_cntr == 'h1 && !b2p_out_eop) ? 1'b1 : 1'b0;
         end
         
         //FIFO data pending error
         if(spim_state[SPIM_START_BIT])
            dbg_wrd_pndng  <= 8'h0;
         else if(dbg_fifo_read && dbg_wrd_pndng != 8'hFF)
            dbg_wrd_pndng  <= dbg_wrd_pndng + 1'b1;
      end
   end : fsm_dbg_seq
   
   always_comb
   begin : fsm_dbg_comb
      dbg_fifo_read = spim_state[SPIM_COMPLETE_BIT] & fifo_out_valid & !fifo_out_sop;
   end : fsm_dbg_comb
   
end else begin //SPI_DEBUG_EN == 0

   assign time_out = 1'b0;
   assign dbg_fifo_read = 1'b0;
   
end
endgenerate

//------------------------------------------------------------------------------
// Packets to bytes IP to generate byte stream from packet (AVST).
// Below special characters are used to indicate packet in byte stream.
//    0x7A - Start of packet indication (byte following 0x7A will be first byte)
//    0x7B - End of packet indication (byte following 0x7B will be last byte)
//    0x7C - Channel selector (byte following 0x7C will be the channel number)
//    0x7D - Escape character 
//------------------------------------------------------------------------------
altera_avalon_st_packets_to_bytes #(
   .CHANNEL_WIDTH (8),
   .ENCODING      (0)
) pkts_to_bytes (
   .clk              (clk              ),
   .reset_n          (~reset           ),
   .in_ready         (p2b_in_ready     ),
   .in_valid         (p2b_in_valid     ),
   .in_data          (p2b_in_data      ),
   .in_channel       (8'h0             ),//(p2b_in_channel   ),
   .in_startofpacket (p2b_in_sop       ),
   .in_endofpacket   (p2b_in_eop       ),
   .out_ready        (p2b_out_ready    ),
   .out_valid        (p2b_out_valid    ),
   .out_data         (p2b_out_data     ) 
);

//------------------------------------------------------------------------------
// Bytes to packets IP to packetize the incoming byte stream.  
//------------------------------------------------------------------------------
altera_avalon_st_bytes_to_packets #(
   .CHANNEL_WIDTH (8),
   .ENCODING      (0)
) bytes_to_pkts (
   .clk               (clk             ),
   .reset_n           (~reset          ),
   .out_channel       (                ), //(b2p_out_channel ),
   .out_ready         (b2p_out_ready   ),
   .out_valid         (b2p_out_valid   ),
   .out_data          (b2p_out_data    ),
   .out_startofpacket (b2p_out_sop     ),
   .out_endofpacket   (b2p_out_eop     ),
   .in_ready          (b2p_in_ready    ),
   .in_valid          (b2p_in_valid    ),
   .in_data           (b2p_in_data     ) 
);

//------------------------------------------------------------------------------
// SPI master SCLK and CSN generation
// Shift MOSI @ rising edge of SCLK and capture MISO @ falling edge
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : spi_ctrl_seq
   if(reset) begin
      clk_cntr       <= 'd0;
      spim_clk_r1    <= 1'b0;
      spim_clk       <= 1'b0;
      spim_csn       <= 1'b1;
      first_sclk     <= 1'b0;
      miso_byte_en   <= 1'b0;
      clk_pedge      <= 1'b0;
      clk_nedge      <= 'd0;
   end else begin
      //SPI SCLK, CS_N and control generation
      if(stop_spi) begin
         clk_cntr       <= ctrl_reg[0+:CLK_DIV_WIDTH];
         spim_clk_r1    <= 1'b0;
         spim_clk       <= 1'b0;
         spim_csn       <= 1'b1;
         first_sclk     <= 1'b0;
         miso_byte_en   <= 1'b0;
         clk_pedge      <= 1'b0;
         clk_nedge      <= 'd0;
      end else begin
         spim_clk       <= spim_clk_r1;
         spim_csn       <= 1'b0;
         
         if(clk_nedge[0])
            first_sclk  <= 1'b1;
         
         if(miso_cptr_nedge) //exclude first negedge
            miso_byte_en<= 1'b1;
            
         if(clk_cntr == 'd0) begin
            clk_cntr    <= ctrl_reg[0+:CLK_DIV_WIDTH];
            spim_clk_r1 <= ~spim_clk_r1;
            clk_pedge   <= ~spim_clk_r1 & (first_sclk | clk_nedge[0]);
            clk_nedge   <= {clk_nedge[MISO_CAPT_DLY-1:0], spim_clk_r1};
         end else begin
            clk_cntr    <= clk_cntr - 1'b1;
            clk_pedge   <= 1'b0;
            clk_nedge   <= {clk_nedge[MISO_CAPT_DLY-1:0], 1'b0};
         end
      end
   end
end : spi_ctrl_seq   

always_comb
begin : spi_ctrl_comb
   miso_cptr_nedge = clk_nedge[ctrl_reg[8+:(MISO_DLY_WIDTH+1)]];
end : spi_ctrl_comb

//------------------------------------------------------------------------------
// SPI master MOSI generation logic
//    - 0x4A is used as IDLE character and is used when there is no data to send
//    - 0x4D is used as ESCAPE character and is used when data contains special
//      charaters (i.e. 0x4A or 0x4D)
//------------------------------------------------------------------------------
assign spim_mosi = mosi_shift_reg[7];

always_ff @(posedge clk, posedge reset)
begin : spi_mosi_seq
   if(reset) begin
      p2b_out_ready  <= 1'b0;
      mosi_shift_reg <= 8'h0;
      mosi_bit_cntr  <= 3'h0;
      mosi_data_byte <= 8'h0;
      esc_sent       <= 1'b0;
      tx_end_n       <= 1'b0;
   end else begin
      if(stop_spi) begin
         p2b_out_ready  <= 1'b0;
         mosi_shift_reg <= 8'h4A;
         mosi_bit_cntr  <= 3'h0;
         mosi_data_byte <= 8'h0;
         esc_sent       <= 1'b0;
         if (spim_state[SPIM_READY_BIT])
            tx_end_n    <= 1'b1;
      end else begin
         //MOSI data bayte latching
         p2b_out_ready  <= 1'b0;
         if(clk_cntr == 'd0 && !spim_clk_r1 && mosi_bit_cntr == 3'd7) begin
            if(p2b_out_valid && (p2b_out_data == 8'h4A || p2b_out_data == 8'h4D) && !esc_sent) begin
               mosi_data_byte <= 8'h4D; //send escape
               esc_sent       <= 1'b1;
            end else if(p2b_out_valid && (p2b_out_data == 8'h4A || p2b_out_data == 8'h4D)) begin
               mosi_data_byte <= p2b_out_data ^ 8'h20; //send modified escaped data
               p2b_out_ready  <= 1'b1;
               esc_sent       <= 1'b0;
            end else if(p2b_out_valid) begin
               mosi_data_byte <= p2b_out_data; //send data
               p2b_out_ready  <= 1'b1;
               esc_sent       <= 1'b0;
            end else begin
               mosi_data_byte <= 8'h4A; //send IDLE
               esc_sent       <= 1'b0;
               tx_end_n       <= 1'b0;
            end
         end
         
         //MOSI shifting
         if(clk_pedge) begin
            if(mosi_bit_cntr == 3'd7)
               mosi_shift_reg <= mosi_data_byte;
            else
               mosi_shift_reg <= {mosi_shift_reg[6:0], 1'b0};
            mosi_bit_cntr <= mosi_bit_cntr + 1'b1;
         end
      end
   end
end : spi_mosi_seq

//------------------------------------------------------------------------------
// SPI master MISO decode logic
//    - 0x4A is used as IDLE character and is discarded
//    - 0x4D is used as ESCAPE character and is also discarded and next 
//      character is XORed with 0x20
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : spi_miso_seq
   if(reset) begin
      miso_bit_cntr  <= 3'h0;
      miso_data_byte <= 8'h0;
      b2p_in_valid   <= 1'b0;
      b2p_in_data    <= 8'h0;
      esc_rcvd       <= 1'b0;
   end else begin
      if(stop_spi) begin
         miso_bit_cntr  <= 3'h0;
         miso_data_byte <= 8'h0;
         b2p_in_valid   <= 1'b0;
         b2p_in_data    <= 8'h0;
         esc_rcvd       <= 1'b0;
      end else begin
         //SPI MISO latching
         if(miso_cptr_nedge) begin
            miso_data_byte <= {miso_data_byte[6:0], spim_miso};
            miso_bit_cntr  <= miso_bit_cntr + 1'b1;
         end
         
         //SPI Rx/MISO data forwarding
         if(miso_bit_cntr == 3'd0 && miso_cptr_nedge && miso_byte_en) begin
            if(miso_data_byte == 8'h4A) begin
               esc_rcvd     <= 1'b0;
               b2p_in_valid <= 1'b0;
            end else if (miso_data_byte == 8'h4D) begin
               esc_rcvd     <= 1'b1;
               b2p_in_valid <= 1'b0;
            end else if (esc_rcvd) begin
               esc_rcvd     <= 1'b0;
               b2p_in_valid <= 1'b1;
               b2p_in_data  <= miso_data_byte ^ 8'h20;
            end else begin
               esc_rcvd     <= 1'b0;
               b2p_in_valid <= 1'b1;
               b2p_in_data  <= miso_data_byte;
            end
         end else if (b2p_in_ready) begin
            b2p_in_valid <= 1'b0;
         end
      end
   end
end : spi_miso_seq   

//------------------------------------------------------------------------------
// SPI Tx/Rx disable logic.
// Briefly deassert CSN between command and response to align slave's response
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin
   if(reset)
      spi_pause_cntr <= 4'd0;
   else if(tx_end_n)
      spi_pause_cntr <= 4'd0;
   else if(!spi_pause_cntr[3])
      spi_pause_cntr <= spi_pause_cntr + 1'd1;
end

always_comb 
begin
   stop_spi = spim_state[SPIM_READY_BIT] | (~spi_pause_cntr[3] & ~tx_end_n);
end

endmodule
