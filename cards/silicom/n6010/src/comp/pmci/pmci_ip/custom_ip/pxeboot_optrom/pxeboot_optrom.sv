// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// This module acts as a OptionROM of the PXEboot flow.
// This module reads the OptionROM contents from FPGA flash on every 
// configuration and stores it in the internal buffer. Host BIOS will read 
// this buffer for OptionROM contents.
//-----------------------------------------------------------------------------

module pxeboot_optrom #(
   parameter   OPTROM_AREA_BADDR    = 32'h0B80_0000, //in OPTROM_SIZE boundary
   parameter   FLASH_ADDR_WIDTH     = 28, //28=2Gb (flash side AvMM master address size)
   parameter   HOST_RDADDR_WIDTH    = 16, //16=64KB  (host side AvMM slave address size)
   parameter   OPTROM_SIZE          = 32  //OptionROM actual size in KBytes
)(
   input  logic                           clk,
   input  logic                           reset,

   //CSR interface
   input  logic                           pxeboot_rd_start,
   output logic [31:0]                    pxeboot_status,

   //AVMM slave (host side)
   input  logic [HOST_RDADDR_WIDTH-4:0]   avmm_slv_addr,
   input  logic                           avmm_slv_read,
   output logic [63:0]                    avmm_slv_rddata,
   output logic                           avmm_slv_rddvld,
   output logic                           avmm_slv_waitreq,
   
   //AVMM master to flash
   output logic [FLASH_ADDR_WIDTH-1:0]    avmm_mstr_addr,
   output logic                           avmm_mstr_read,
   output logic [6:0]                     avmm_mstr_burstcnt,
   input  logic [31:0]                    avmm_mstr_rddata,
   input  logic                           avmm_mstr_rddvld,
   input  logic                           avmm_mstr_waitreq
);


localparam OPTROM_DW_SIZE   = OPTROM_SIZE*1024/4;
localparam OPTROM_AWID      = $clog2(OPTROM_DW_SIZE);
localparam OPTROM_DEPTH     = 2**OPTROM_AWID;
localparam DIS_OPTROM       = "YES"; //Disable PXEboot OROM logic & buffer = YES, NO

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// PXEboot OptionROM Enabled
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
generate 
if (DIS_OPTROM == "NO") begin
//------------------------------------------------------------------------------
// Internal Declarations
//------------------------------------------------------------------------------
enum {
   OPTROM_RESET_BIT     = 0,
   OPTROM_READY_BIT     = 1,
   OPTROM_RD_REQ_BIT    = 2,
   OPTROM_RD_DATA_BIT   = 3,
   OPTROM_RD_DONE_BIT   = 4
   
} optrom_state_bit;

enum logic [4:0] {
   OPTROM_RESET_ST      = 5'h1 << OPTROM_RESET_BIT   ,
   OPTROM_READY_ST      = 5'h1 << OPTROM_READY_BIT   ,
   OPTROM_RD_REQ_ST     = 5'h1 << OPTROM_RD_REQ_BIT  ,
   OPTROM_RD_DATA_ST    = 5'h1 << OPTROM_RD_DATA_BIT ,
   OPTROM_RD_DONE_ST    = 5'h1 << OPTROM_RD_DONE_BIT
} optrom_state, optrom_next;


logic [OPTROM_AWID+1:0]    flsh_rd_offset;
logic                      rd_complete;
logic [63:0]               orom_rddata;
logic                      orom_addr_range;
logic                      orom_rden_r1;
logic                      orom_rden_r2;


//------------------------------------------------------------------------------
// Option ROM copying FSM 
// Top "always_ff" simply switches the state of the state machine registers.
// Following "always_comb" contains all of the next-state decoding logic.
//------------------------------------------------------------------------------
always_ff @(posedge clk)
begin : optrom_sm_seq
   if (reset)
      optrom_state <= OPTROM_RESET_ST;
   else
      optrom_state <= optrom_next;
end : optrom_sm_seq

always_comb
begin : optrom_sm_comb
   optrom_next = optrom_state;
   unique case (1'b1) //Reverse Case Statement
      optrom_state[OPTROM_RESET_BIT]:   //OPTROM_RESET_ST
         if (reset)
            optrom_next = OPTROM_RESET_ST;
         else
            optrom_next = OPTROM_READY_ST;
      
      optrom_state[OPTROM_READY_BIT]:   //OPTROM_READY_ST
         if(pxeboot_rd_start)
            optrom_next = OPTROM_RD_REQ_ST;

      optrom_state[OPTROM_RD_REQ_BIT]: //OPTROM_RD_REQ_ST
         if(rd_complete)
            optrom_next = OPTROM_RD_DONE_ST;
         else
            optrom_next = OPTROM_RD_DATA_ST;
      
      optrom_state[OPTROM_RD_DATA_BIT]: //OPTROM_RD_DATA_ST
         if(flsh_rd_offset[7:2] == 6'd63 && avmm_mstr_rddvld)
            optrom_next = OPTROM_RD_REQ_ST;
      
      optrom_state[OPTROM_RD_DONE_BIT]: //OPTROM_RD_DONE_ST
         optrom_next = OPTROM_RD_DONE_ST;
   endcase
end : optrom_sm_comb


//------------------------------------------------------------------------------
// AvMM master interface (towards flash controller) signal generation
//------------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : fsm_ctrl_seq
   if(reset) begin
      flsh_rd_offset    <= '0;
      avmm_mstr_read    <= 1'b0;
      rd_complete       <= 1'b0;
   end else begin
      if(optrom_state[OPTROM_READY_BIT])
         flsh_rd_offset <= OPTROM_AREA_BADDR;
      else if (optrom_state[OPTROM_RD_DATA_BIT] && avmm_mstr_rddvld)
         flsh_rd_offset <= flsh_rd_offset + 3'd4;
      
      if(optrom_state[OPTROM_RD_REQ_BIT] && !rd_complete)
         avmm_mstr_read    <= 1'b1;
      else if(!avmm_mstr_waitreq)   
         avmm_mstr_read    <= 1'b0;
         
      if(optrom_state[OPTROM_RD_DATA_BIT] && avmm_mstr_rddvld && 
                          (flsh_rd_offset[OPTROM_AWID+1:2] == OPTROM_DW_SIZE-1))
         rd_complete <= 1'b1;
   end
end : fsm_ctrl_seq

always_comb
begin : fsm_ctrl_comb   
 //avmm_mstr_addr                   = OPTROM_AREA_BADDR;
   avmm_mstr_addr[FLASH_ADDR_WIDTH-1:OPTROM_AWID+2] = OPTROM_AREA_BADDR >> (OPTROM_AWID+2);
   avmm_mstr_addr[OPTROM_AWID+1:0]  = flsh_rd_offset;
   avmm_mstr_burstcnt               = 7'd64;
end : fsm_ctrl_comb


//------------------------------------------------------------------------------
// Option ROM
//------------------------------------------------------------------------------
altera_syncram  option_rom (
   .address_a     (flsh_rd_offset[OPTROM_AWID+1:2] ),
   .address_b     (avmm_slv_addr[OPTROM_AWID-2:0]  ),
   .clock0        (clk                             ),
   .data_a        (avmm_mstr_rddata                ),
   .wren_a        (avmm_mstr_rddvld                ),
   .q_b           (orom_rddata                     ),
   .aclr0         (1'b0       ),
   .aclr1         (1'b0       ),
   .address2_a    (1'b1       ),
   .address2_b    (1'b1       ),
   .addressstall_a(1'b0       ),
   .addressstall_b(1'b0       ),
   .byteena_a     (1'b1       ),
   .byteena_b     (1'b1       ),
   .clock1        (1'b1       ),
   .clocken0      (1'b1       ),
   .clocken1      (1'b1       ),
   .clocken2      (1'b1       ),
   .clocken3      (1'b1       ),
   .data_b        ({64{1'b1}} ),
   .eccencbypass  (1'b0       ),
   .eccencparity  (8'b0       ),
   .eccstatus     (           ),
   .q_a           (           ),
   .rden_a        (1'b1       ),
   .rden_b        (1'b1       ),
   .sclr          (1'b0       ),
   .wren_b        (1'b0       )
);
defparam
   option_rom.address_aclr_b  = "NONE",
   option_rom.address_reg_b  = "CLOCK0",
   option_rom.clock_enable_input_a  = "BYPASS",
   option_rom.clock_enable_input_b  = "BYPASS",
   option_rom.clock_enable_output_b  = "BYPASS",
   option_rom.intended_device_family  = "Agilex",
   option_rom.lpm_type  = "altera_syncram",
   option_rom.numwords_a  = OPTROM_DEPTH,
   option_rom.numwords_b  = (OPTROM_DEPTH/2),
   option_rom.operation_mode  = "DUAL_PORT",
   option_rom.outdata_aclr_b  = "NONE",
   option_rom.outdata_sclr_b  = "NONE",
   option_rom.outdata_reg_b  = "CLOCK0",
   option_rom.power_up_uninitialized  = "FALSE",
   option_rom.read_during_write_mode_mixed_ports  = "DONT_CARE",
   option_rom.widthad_a  = OPTROM_AWID,
   option_rom.widthad_b  = (OPTROM_AWID-1),
   option_rom.width_a  = 32,
   option_rom.width_b  = 64,
   option_rom.width_byteena_a  = 1;


//------------------------------------------------------------------------------
// HOst OptionROM reading
//------------------------------------------------------------------------------
assign orom_addr_range = (HOST_RDADDR_WIDTH == OPTROM_AWID+2) ? 1'b1 : 
                           ~(|avmm_slv_addr[HOST_RDADDR_WIDTH-4:OPTROM_AWID-1]);

always_ff @(posedge clk, posedge reset)
begin : host_rd
   if(reset) begin
      orom_rden_r1      <= 1'b0;
      orom_rden_r2      <= 1'b0;
      avmm_slv_rddvld   <= 1'b0;
      avmm_slv_rddata   <= 64'd0;
   end else begin
      if(orom_addr_range && avmm_slv_read)
         orom_rden_r1   <= 1'b1;
      else
         orom_rden_r1   <= 1'b0;
      
      orom_rden_r2 <= orom_rden_r1;
      
      if(!orom_addr_range && avmm_slv_read || orom_rden_r2)
         avmm_slv_rddvld   <= 1'b1;
      else
         avmm_slv_rddvld   <= 1'b0;
      
      if(orom_rden_r2)
         avmm_slv_rddata   <= orom_rddata;
      else
         avmm_slv_rddata   <= '1; //all 1's
   end
end : host_rd

assign avmm_slv_waitreq = 1'b0;


//------------------------------------------------------------------------------
// PXEboot OptionROM status
//------------------------------------------------------------------------------
always_comb
begin : orom_sts   
   pxeboot_status[31:16+OPTROM_AWID] = '0;
   pxeboot_status[16+:OPTROM_AWID]   = flsh_rd_offset[OPTROM_AWID+1:2];
   pxeboot_status[15:13]             = '0;
   pxeboot_status[12:8]              = optrom_state;
   pxeboot_status[7:2]               = '0;
   pxeboot_status[1]                 = rd_complete;
   pxeboot_status[0]                 = pxeboot_rd_start;
end : orom_sts

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// PXEboot OptionROM Disabled
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
end else begin
   assign pxeboot_status       = '0;
   assign avmm_slv_rddata      = '1;
   assign avmm_slv_waitreq     = '0;
   assign avmm_mstr_addr       = '0;
   assign avmm_mstr_read       = '0;
   assign avmm_mstr_burstcnt   = '0;
   
   always_ff @(posedge clk, posedge reset)
   begin : host_rd
      if(reset)
         avmm_slv_rddvld      <= 1'b0;
      else 
         avmm_slv_rddvld      <= avmm_slv_read;
   end : host_rd
end
endgenerate

endmodule
