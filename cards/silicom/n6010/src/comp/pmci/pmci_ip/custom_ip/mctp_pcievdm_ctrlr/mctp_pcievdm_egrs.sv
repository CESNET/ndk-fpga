// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// MCTP over PCIe VDM Egress module receives the MCTP payload from MAX10’s MCTP 
// over PCIe VDM buffer and constructs PCIe VDM TLPs and forwards it to AFU.
//-----------------------------------------------------------------------------

module mctp_pcievdm_egrs #(
   parameter   EGRS_SLV_ADDR_WIDTH     = 9,
   parameter   SS_ADDR_WIDTH           = 21,
   parameter   DEBUG_REG_EN            = 0,
   parameter   DEBUG_REG_WIDTH         = 8,
   parameter   MCTP_HDR_VERSION        = 4'h1,
   parameter   MCTP_BASELINE_MTU       = 16
)(
   input  logic                            clk,
   input  logic                            reset,
   
   //CSR i/f
   input  logic [SS_ADDR_WIDTH-1:0]        pcievdm_afu_addr,
   input  logic [7:0]                      pcievdm_mctp_eid,
   output logic [63:0]                     pcie_vdm_sts4_dbg,
   output logic [63:0]                     pcie_vdm_sts5_dbg,
   input  logic                            pulse_1us,
   
   //Egress AVMM slave (connected to SPI Slave)
   input  logic [EGRS_SLV_ADDR_WIDTH-1:0]  avmm_egrs_slv_addr,
   input  logic                            avmm_egrs_slv_write,
   input  logic                            avmm_egrs_slv_read,
   input  logic [31:0]                     avmm_egrs_slv_wrdata,
   output logic [31:0]                     avmm_egrs_slv_rddata,
   output logic                            avmm_egrs_slv_rddvld,
   output logic                            avmm_egrs_slv_waitreq,

   //Egress AVMM Master (connected to IOFS-shell/AFU)
   output logic [SS_ADDR_WIDTH-1:0]        avmm_egrs_mstr_addr,
   output logic                            avmm_egrs_mstr_write,
   output logic                            avmm_egrs_mstr_read,
   output logic [63:0]                     avmm_egrs_mstr_wrdata,
   output logic [7:0]                      avmm_egrs_mstr_byteen,
   input  logic [63:0]                     avmm_egrs_mstr_rddata,
   input  logic                            avmm_egrs_mstr_rddvld,
   input  logic                            avmm_egrs_mstr_waitreq
);

localparam  EGRS_CNS_REG_ADDR    = 9'd0; //PMCI Tx Control and status register address
localparam  EGRS_PH_REG_ADDR     = 9'd1; //PMCI Tx Packet Header register address
localparam  EGRS_BFR_AMSB        = 8;    //PMCI Tx Buffer base address bit
localparam  TLP_NO_SNOOP_ATTR    = 1'b0; //PCIe TLP header Attr[0] field
localparam  MCTP_BLMTU_BYTES     = MCTP_BASELINE_MTU * 4;  //MCTP baseline MTU size in bytes
localparam  TLP_LEN_WIDTH        = $clog2(MCTP_BASELINE_MTU+1);//TLP length width max


//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
enum {
   EGRS_RESET_BIT   = 0,
   EGRS_IDLE_BIT    = 1,
   EGRS_AFU_RDY_BIT = 2,
   EGRS_SOP_BIT     = 3,
   EGRS_HDR_1_BIT   = 4,
   EGRS_HDR_2_BIT   = 5,
   EGRS_PLOAD_BIT   = 6,
   EGRS_EOP_BIT     = 7,
   EGRS_WAIT_BIT    = 8
} egrs_state_bit;

enum logic [8:0] {
   EGRS_RESET_ST    = 9'h1 << EGRS_RESET_BIT  ,
   EGRS_IDLE_ST     = 9'h1 << EGRS_IDLE_BIT   ,
   EGRS_AFU_RDY_ST  = 9'h1 << EGRS_AFU_RDY_BIT,
   EGRS_SOP_ST      = 9'h1 << EGRS_SOP_BIT    ,
   EGRS_HDR_1_ST    = 9'h1 << EGRS_HDR_1_BIT  ,
   EGRS_HDR_2_ST    = 9'h1 << EGRS_HDR_2_BIT  ,
   EGRS_PLOAD_ST    = 9'h1 << EGRS_PLOAD_BIT  ,
   EGRS_EOP_ST      = 9'h1 << EGRS_EOP_BIT    ,
   EGRS_WAIT_ST     = 9'h1 << EGRS_WAIT_BIT   
} egrs_state, egrs_next, egrs_state_r1;

logic                      mctp_msg_rdy_reg  ;
logic [8:0]                mctp_msg_len_reg  ;
logic [1:0]                tlp_pad_len_reg   ;
logic [15:0]               tlp_trgt_id_reg   ;
logic [7:0]                mctp_dst_eid_reg  ;
logic [3:0]                mctp_tag_reg      ;
logic [7:0]                mctp_src_eid_reg  ;
logic [2:0]                tlp_pcie_route_reg;
logic [EGRS_BFR_AMSB-1:0]  egrs_bfr_wraddr   ;
logic [31:0]               egrs_bfr_wrdata   ;
logic                      egrs_bfr_wren     ;
logic [31:0]               egrs_bfr_rddata   ;
logic                      bufr_rd_vld1      ;
logic                      bufr_rd_vld2      ;
logic                      bufr_rd_vld3      ;
logic [EGRS_BFR_AMSB-1:0]  egrs_bfr_rdaddr   ;
logic [31:0]               egrs_bfr_rddata_r1;
logic                      pkt_rd_done       ;
logic                      not_last_pkt      ;
logic [8:0]                mctp_pndng_len    ;
logic [TLP_LEN_WIDTH-1:0]  tlp_payload_len   ;
logic [1:0]                tlp_pad_len       ;
logic                      mctp_pkt_som      ;
logic                      mctp_pkt_eom      ;
logic [1:0]                mctp_pkt_seq      ;
logic                      dly_busy_rechk    ;
logic [9:0]                pcie_tlp_len      ;
logic [63:0]               pcie_tlp_hdr_1    ;
logic [63:0]               pcie_tlp_hdr_2    ;


//-----------------------------------------------------------------------------
//Egress Tx Control Register - address 0x0
//    [0]      RW    Tx packet available in Tx buffer.
//    [1]      R     PCIeVDM Transmitter module (RTL module) is busy
//    [3:2]    R     Reserved
//    [5:4]    RW    Tx packet pad length (0 – no padding, 1 – one 0x00 padding, etc)
//    [15:6]   RW    Tx packet size in DWORDs (actual size is 1KB max)
//    [31:16]  R     Reserved
//Egress Tx Packet Header - address 0x4
//    [15:0]   RW    PCIe target ID of Tx packet
//    [23:16]  RW    Destination EID of Tx packet
//    [26:24]  RW    Message tag of Tx MCTP packet
//    [27]     RW    TO bit of Tx MCTP packet
//    [28]     RW    Null Source EID (1-null EID; 0-configured EID)
//    [29]     RW    PCIe VDM routing (0-route to root complex, 1-route by ID)
//    [31:28]  R     Reserved
//Egress Tx Packet Buffer - address 0x400 ~ 0x7FC 
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : xmtr_reg_wr
   if(reset) begin
      mctp_msg_rdy_reg   <= 1'b0;
      mctp_msg_len_reg   <= 9'd0;
      tlp_pad_len_reg    <= 2'd0;
      tlp_trgt_id_reg    <= 16'd0;
      mctp_dst_eid_reg   <= 8'd0;
      mctp_tag_reg       <= 4'd0;
      mctp_src_eid_reg   <= 8'd0;
      tlp_pcie_route_reg <= 3'd0;
   end else begin
      if(avmm_egrs_slv_addr == EGRS_CNS_REG_ADDR && avmm_egrs_slv_write && 
                                            egrs_state[EGRS_IDLE_BIT]) begin
         mctp_msg_rdy_reg   <= avmm_egrs_slv_wrdata[0];
         mctp_msg_len_reg   <= avmm_egrs_slv_wrdata[14:6];
         tlp_pad_len_reg    <= avmm_egrs_slv_wrdata[5:4];
      end else
         mctp_msg_rdy_reg   <= 1'b0;
      
      if(avmm_egrs_slv_addr == EGRS_PH_REG_ADDR && avmm_egrs_slv_write && 
                                                egrs_state[EGRS_IDLE_BIT]) begin
         tlp_trgt_id_reg    <= avmm_egrs_slv_wrdata[29] ? avmm_egrs_slv_wrdata[15:0] : 16'd0;
         mctp_dst_eid_reg   <= avmm_egrs_slv_wrdata[23:16];
         mctp_tag_reg       <= avmm_egrs_slv_wrdata[27:24];
         mctp_src_eid_reg   <= avmm_egrs_slv_wrdata[28] ? 8'h00 : pcievdm_mctp_eid;
         tlp_pcie_route_reg <= avmm_egrs_slv_wrdata[29] ? 3'd2 : 3'd0;
      end
   end 
end : xmtr_reg_wr

always_ff @(posedge clk, posedge reset)
begin : xmtr_reg_rd
   if(reset) begin
      avmm_egrs_slv_rddvld    <= 1'b0;
      avmm_egrs_slv_rddata    <= 32'd0;
      avmm_egrs_slv_waitreq   <= 1'b1;
   end else begin
      avmm_egrs_slv_rddvld    <= avmm_egrs_slv_read;
      avmm_egrs_slv_rddata    <= {30'd0, ~egrs_state[EGRS_IDLE_BIT], 1'b0};
      avmm_egrs_slv_waitreq   <= 1'b0;
   end
end : xmtr_reg_rd

//-----------------------------------------------------------------------------
// Egress Buffer Write Logic
//-----------------------------------------------------------------------------
always_comb
begin : egrs_bfr_wr
   egrs_bfr_wraddr = avmm_egrs_slv_addr[EGRS_BFR_AMSB-1:0];
   egrs_bfr_wrdata = avmm_egrs_slv_wrdata; 
   egrs_bfr_wren   = egrs_state[EGRS_IDLE_BIT] & avmm_egrs_slv_write & 
                                          avmm_egrs_slv_addr[EGRS_BFR_AMSB]; 
end : egrs_bfr_wr

//-----------------------------------------------------------------------------
// Egress Buffer Instantiation
//-----------------------------------------------------------------------------
altera_syncram egress_buffer 
(
   .clock0           (clk              ),
   .address_a        (egrs_bfr_wraddr  ),
   .address_b        (egrs_bfr_rdaddr  ),
   .data_a           (egrs_bfr_wrdata  ),
   .wren_a           (egrs_bfr_wren    ),
   .q_b              (egrs_bfr_rddata  ),
   .aclr0            (1'b0             ),
   .aclr1            (1'b0             ),
   .address2_a       (1'b1             ),
   .address2_b       (1'b1             ),
   .addressstall_a   (1'b0             ),
   .addressstall_b   (1'b0             ),
   .byteena_a        (1'b1             ),
   .byteena_b        (1'b1             ),
   .clock1           (1'b1             ),
   .clocken0         (1'b1             ),
   .clocken1         (1'b1             ),
   .clocken2         (1'b1             ),
   .clocken3         (1'b1             ),
   .data_b           ({32{1'b1}}       ),
   .eccencbypass     (1'b0             ),
   .eccencparity     (8'b0             ),
   .eccstatus        (                 ),
   .q_a              (                 ),
   .rden_a           (1'b1             ),
   .rden_b           (1'b1             ),
   .sclr             (1'b0             ),
   .wren_b           (1'b0             )
);

defparam
   egress_buffer.address_aclr_b          = "NONE",
   egress_buffer.address_reg_b           = "CLOCK0",
   egress_buffer.clock_enable_input_a    = "BYPASS",
   egress_buffer.clock_enable_input_b    = "BYPASS",
   egress_buffer.clock_enable_output_b   = "BYPASS",
   egress_buffer.intended_device_family  = "Agilex",
   egress_buffer.lpm_type                = "altera_syncram",
   egress_buffer.numwords_a              = 256,
   egress_buffer.numwords_b              = 256,
   egress_buffer.operation_mode          = "DUAL_PORT",
   egress_buffer.outdata_aclr_b          = "NONE",
   egress_buffer.outdata_sclr_b          = "NONE",
   egress_buffer.outdata_reg_b           = "CLOCK0",
   egress_buffer.power_up_uninitialized  = "FALSE",
   egress_buffer.read_during_write_mode_mixed_ports  = "DONT_CARE",
   egress_buffer.widthad_a               = 8,
   egress_buffer.widthad_b               = 8,
   egress_buffer.width_a                 = 32,
   egress_buffer.width_b                 = 32,
   egress_buffer.width_byteena_a         = 1;


//-----------------------------------------------------------------------------
// Egress PCIe VDM TLP FSM.
// This FSM reads the MCTP payload from egress buffer and constructs MCTP over 
// PCIe VDM TLP and then forwards it to AFU .
// Top "always_ff" simply switches the state of the state machine registers.
// Following "always_comb" contains all of the next-state decoding logic.
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : egrs_fsm_seq
   if (reset) begin
      egrs_state     <= EGRS_RESET_ST;
      egrs_state_r1  <= EGRS_RESET_ST;
   end else begin
      egrs_state     <= egrs_next;
      egrs_state_r1  <= egrs_state;
   end
end : egrs_fsm_seq

always_comb
begin : egrs_fsm_comb
   egrs_next = egrs_state;
   unique case (1'b1) //Reverse Case Statement
      egrs_state[EGRS_RESET_BIT]:   //EGRS_RESET_ST
         if (reset)
            egrs_next = EGRS_RESET_ST;
         else
            egrs_next = EGRS_IDLE_ST;
            
      egrs_state[EGRS_IDLE_BIT]:    //EGRS_IDLE_ST   
         if(mctp_msg_rdy_reg)
            egrs_next = EGRS_AFU_RDY_ST;
            
      egrs_state[EGRS_AFU_RDY_BIT]: //EGRS_AFU_RDY_ST
         if(avmm_egrs_mstr_rddvld && !avmm_egrs_mstr_rddata[2])
            egrs_next = EGRS_SOP_ST;

      egrs_state[EGRS_SOP_BIT]:     //EGRS_SOP_ST    
         if(avmm_egrs_mstr_write && !avmm_egrs_mstr_waitreq)
            egrs_next = EGRS_HDR_1_ST;

      egrs_state[EGRS_HDR_1_BIT]:   //EGRS_HDR_1_ST  
         if(avmm_egrs_mstr_write && !avmm_egrs_mstr_waitreq)
            egrs_next = EGRS_HDR_2_ST;

      egrs_state[EGRS_HDR_2_BIT]:   //EGRS_HDR_2_ST  
         if(avmm_egrs_mstr_write && !avmm_egrs_mstr_waitreq)
            egrs_next = EGRS_PLOAD_ST;

      egrs_state[EGRS_PLOAD_BIT]:   //EGRS_PLOAD_ST  
         if(pkt_rd_done && avmm_egrs_mstr_write && !avmm_egrs_mstr_waitreq)
            egrs_next = EGRS_EOP_ST;

      egrs_state[EGRS_EOP_BIT]:     //EGRS_EOP_ST    
         if(avmm_egrs_mstr_write && !avmm_egrs_mstr_waitreq) begin
             if(not_last_pkt)
               egrs_next = EGRS_WAIT_ST; //EGRS_AFU_RDY_ST;
            else
               egrs_next = EGRS_IDLE_ST;
         end 
         
      egrs_state[EGRS_WAIT_BIT]:    //EGRS_WAIT_ST   
         if(pulse_1us)
            egrs_next = EGRS_AFU_RDY_ST;

   endcase
end : egrs_fsm_comb


//-----------------------------------------------------------------------------
// Egress Buffer Read Logic
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : egrs_bfr_rd
   if (reset) begin
      bufr_rd_vld1      <= 1'b0;
      bufr_rd_vld2      <= 1'b0;
      bufr_rd_vld3      <= 1'b0;
      egrs_bfr_rdaddr   <= 8'd0;
      egrs_bfr_rddata_r1<= 32'd0;
      pkt_rd_done       <= 1'b0;
   end else begin
      //if(egrs_state[EGRS_IDLE_BIT])
      //   egrs_bfr_rdaddr   <= 8'd0;
      //else if(egrs_state[EGRS_PLOAD_BIT] && (!avmm_egrs_mstr_write || !avmm_egrs_mstr_waitreq))
      //   egrs_bfr_rdaddr   <= egrs_bfr_rdaddr + 8'd1;
      //
      //if(!egrs_state[EGRS_PLOAD_BIT]) begin
      //   bufr_rd_vld1 <= 1'b0;
      //   bufr_rd_vld2 <= 1'b0;
      //   bufr_rd_vld3 <= 1'b0;
      //end else if(!avmm_egrs_mstr_write || !avmm_egrs_mstr_waitreq) begin
      //   bufr_rd_vld1 <= ~bufr_rd_vld1;
      //   bufr_rd_vld2 <= bufr_rd_vld1;
      //   bufr_rd_vld3 <= bufr_rd_vld2;
      //end

      if(!egrs_state[EGRS_PLOAD_BIT])
         bufr_rd_vld1    <= 1'b0;
      else if(!avmm_egrs_mstr_write && !bufr_rd_vld1 && !bufr_rd_vld2 && !bufr_rd_vld3)
         bufr_rd_vld1    <= 1'b1;
      else
         bufr_rd_vld1    <= 1'b0;
      
      if(egrs_state[EGRS_IDLE_BIT])
         egrs_bfr_rdaddr   <= 8'd0;
      else if(egrs_state[EGRS_PLOAD_BIT] && !avmm_egrs_mstr_write && 
                                 !bufr_rd_vld2 && !bufr_rd_vld3 && !pkt_rd_done)
         egrs_bfr_rdaddr   <= egrs_bfr_rdaddr + 8'd1;
      
      bufr_rd_vld2       <= bufr_rd_vld1;
      bufr_rd_vld3       <= bufr_rd_vld2;
      egrs_bfr_rddata_r1 <= egrs_bfr_rddata;
         
      if(!egrs_state[EGRS_PLOAD_BIT])
         pkt_rd_done    <= 1'b0;
      else if(!avmm_egrs_mstr_write && !bufr_rd_vld1 && !bufr_rd_vld2 && 
              !bufr_rd_vld3 && tlp_payload_len == 'd1 || tlp_payload_len == 'd0)
         pkt_rd_done    <= 1'b1;
   end
end : egrs_bfr_rd


//-----------------------------------------------------------------------------
// MCTP header flag generation
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : mctp_flgs
   if (reset) begin
      not_last_pkt      <= 1'b0;
      mctp_pndng_len    <= 9'd0;
      tlp_payload_len   <= {TLP_LEN_WIDTH{1'b0}};
      tlp_pad_len       <= 2'd0;
      mctp_pkt_som      <= 1'b0;
      mctp_pkt_eom      <= 1'b0;
      mctp_pkt_seq      <= 2'd0;
   end else begin
      if(mctp_pndng_len > MCTP_BASELINE_MTU)
         not_last_pkt   <= 1'b1;
      else
         not_last_pkt   <= 1'b0;
         
      if(egrs_state[EGRS_IDLE_BIT])
         mctp_pndng_len  <= mctp_msg_len_reg;
      else if(egrs_state[EGRS_WAIT_BIT] && !egrs_state_r1[EGRS_WAIT_BIT])
         mctp_pndng_len  <= mctp_pndng_len - MCTP_BASELINE_MTU;

      if(!egrs_state[EGRS_PLOAD_BIT] && not_last_pkt)
         tlp_payload_len <= MCTP_BASELINE_MTU;
      else if(!egrs_state[EGRS_PLOAD_BIT])
         tlp_payload_len <= mctp_pndng_len[TLP_LEN_WIDTH-1:0];
      else if(bufr_rd_vld1 || bufr_rd_vld2)
         tlp_payload_len <= tlp_payload_len - 1'b1;

      if(egrs_state[EGRS_SOP_BIT] && not_last_pkt)
         tlp_pad_len     <= 2'd0;
      else if(egrs_state[EGRS_SOP_BIT])
         tlp_pad_len     <= tlp_pad_len_reg;
         
      if(egrs_state[EGRS_IDLE_BIT])
         mctp_pkt_som   <= 1'b1;
      else if (egrs_state[EGRS_PLOAD_BIT])
         mctp_pkt_som   <= 1'b0;
      
      if(egrs_state[EGRS_HDR_1_BIT] && not_last_pkt)
         mctp_pkt_eom   <= 1'b0;
      else if (egrs_state[EGRS_HDR_1_BIT])
         mctp_pkt_eom   <= 1'b1;
      
      if (egrs_state[EGRS_EOP_BIT] && avmm_egrs_mstr_write && !avmm_egrs_mstr_waitreq)
         mctp_pkt_seq   <= mctp_pkt_seq + 1'b1;
   end
end : mctp_flgs


//-----------------------------------------------------------------------------
// Egress AVMM Master generation
//-----------------------------------------------------------------------------
always_comb
begin : egrs_tlp_hdr
   pcie_tlp_len   = {{(10-TLP_LEN_WIDTH){1'b0}}, tlp_payload_len};
   
   pcie_tlp_hdr_1 = {8'h7F,                                            //Byte-7
                     2'd0, tlp_pad_len, 4'd0,                          //Byte-6
                     16'd0,                                            //Byte-5 & 4
                     pcie_tlp_len[7:0],                                //Byte-3
                     3'd0, TLP_NO_SNOOP_ATTR, 2'd0, pcie_tlp_len[9:8], //Byte-2
                     8'd0,                                             //Byte-1
                     5'h0E, tlp_pcie_route_reg};                       //Byte-0
                     
                     
                     
   pcie_tlp_hdr_2 = {mctp_pkt_som, mctp_pkt_eom, mctp_pkt_seq, mctp_tag_reg, //Byte-7
                     mctp_src_eid_reg,        //Byte-6
                     mctp_dst_eid_reg,        //Byte-5
                     4'h0, MCTP_HDR_VERSION,  //Byte-4
                     8'hB4,                   //Byte-3
                     8'h1A,                   //Byte-2
                     tlp_trgt_id_reg[7:0],    //Byte-1
                     tlp_trgt_id_reg[15:8]};  //Byte-0
                     
end : egrs_tlp_hdr

always_ff @(posedge clk, posedge reset)
begin : egrs_avmm_mstr
   if (reset) begin
      avmm_egrs_mstr_read     <= 1'b0;
      avmm_egrs_mstr_write    <= 1'b0;
      avmm_egrs_mstr_addr     <= {SS_ADDR_WIDTH{1'b0}};
      avmm_egrs_mstr_wrdata   <= 64'd0;
      avmm_egrs_mstr_byteen   <= 8'd0;
      dly_busy_rechk          <= 1'b0;
   end else begin
      if(egrs_state[EGRS_AFU_RDY_BIT] && avmm_egrs_mstr_rddvld && avmm_egrs_mstr_rddata[2])
         dly_busy_rechk       <= 1'b1;
      else if(pulse_1us)
         dly_busy_rechk       <= 1'b0;
      
      if(egrs_state[EGRS_AFU_RDY_BIT] && !egrs_state_r1[EGRS_AFU_RDY_BIT] ||
         egrs_state[EGRS_AFU_RDY_BIT] && dly_busy_rechk && pulse_1us)
         avmm_egrs_mstr_read     <= 1'b1;
      else if(!avmm_egrs_mstr_waitreq)
         avmm_egrs_mstr_read     <= 1'b0;
      
      if(egrs_state[EGRS_SOP_BIT] && !egrs_state_r1[EGRS_SOP_BIT] ||
         egrs_state[EGRS_HDR_1_BIT] && !egrs_state_r1[EGRS_HDR_1_BIT] || 
         egrs_state[EGRS_HDR_2_BIT] && !egrs_state_r1[EGRS_HDR_2_BIT] ||
         egrs_state[EGRS_PLOAD_BIT] && bufr_rd_vld3 || 
         egrs_state[EGRS_EOP_BIT] && !egrs_state_r1[EGRS_EOP_BIT])
         avmm_egrs_mstr_write    <= 1'b1;
      else if(!avmm_egrs_mstr_waitreq)
         avmm_egrs_mstr_write    <= 1'b0;
         
      if(egrs_state[EGRS_HDR_1_BIT] || egrs_state[EGRS_HDR_2_BIT] || 
                                       egrs_state[EGRS_PLOAD_BIT])
         avmm_egrs_mstr_addr  <= {pcievdm_afu_addr[SS_ADDR_WIDTH-1:4], 4'd8};
      else 
         avmm_egrs_mstr_addr  <= {pcievdm_afu_addr[SS_ADDR_WIDTH-1:4], 4'd0};
         
      if(egrs_state[EGRS_HDR_1_BIT])
         avmm_egrs_mstr_wrdata <= pcie_tlp_hdr_1;
      else if(egrs_state[EGRS_HDR_2_BIT])
         avmm_egrs_mstr_wrdata <= pcie_tlp_hdr_2;
      else if(egrs_state[EGRS_PLOAD_BIT] && bufr_rd_vld3)
         avmm_egrs_mstr_wrdata <= {egrs_bfr_rddata, egrs_bfr_rddata_r1};
      else if(!egrs_state[EGRS_PLOAD_BIT]) 
         avmm_egrs_mstr_wrdata <= {62'd0, 
                                   egrs_state[EGRS_EOP_BIT], 
                                   egrs_state[EGRS_SOP_BIT]};
      
      if(!egrs_state[EGRS_PLOAD_BIT])
         avmm_egrs_mstr_byteen <= 8'hFF;
      else if(tlp_payload_len == 'd1 && bufr_rd_vld1)
         avmm_egrs_mstr_byteen <= 8'h0F;
   end
end : egrs_avmm_mstr


//-----------------------------------------------------------------------------
// Debug registers
//-----------------------------------------------------------------------------
generate 
if (DEBUG_REG_EN == 1) begin
   logic [DEBUG_REG_WIDTH-2:0] msg_rx_cntr_dbg_i  ;
   logic                       msg_rx_of_dbg_i    ;
   logic [DEBUG_REG_WIDTH-2:0] tlp_tx_cntr_dbg_i  ;
   logic                       tlp_tx_of_dbg_i    ;
   
   always_ff @(posedge clk, posedge reset)
   begin : dbg_reg
      if (reset) begin
         msg_rx_cntr_dbg_i   <= 'd0;
         msg_rx_of_dbg_i     <= 1'b0;
         tlp_tx_cntr_dbg_i   <= 'd0;
         tlp_tx_of_dbg_i     <= 1'b0;
      end else begin
         //Total number of MCTP messages received
         if(mctp_msg_rdy_reg)
            msg_rx_cntr_dbg_i <= msg_rx_cntr_dbg_i + 1'b1;
         
         if(mctp_msg_rdy_reg && (&msg_rx_cntr_dbg_i))
            msg_rx_of_dbg_i   <= 1'b1;
         
         //Total number of TLPs transmitted
         if(egrs_state[EGRS_EOP_BIT] && 
                                avmm_egrs_mstr_write && !avmm_egrs_mstr_waitreq)
            tlp_tx_cntr_dbg_i <= tlp_tx_cntr_dbg_i + 1'b1;
         
         if(egrs_state[EGRS_EOP_BIT] && avmm_egrs_mstr_write && 
                                !avmm_egrs_mstr_waitreq && (&tlp_tx_cntr_dbg_i))
            tlp_tx_of_dbg_i   <= 1'b1;
      end
   end : dbg_reg
   
   assign pcie_vdm_sts4_dbg       = {55'd0,
                                     egrs_state};     //[8:0]  - Egress FSM state
   
   //[63:32] - Reserved
   //[31:16] - Number of MCTP message received
   //[15:0]  - Number of TLPs transmitted
   assign pcie_vdm_sts5_dbg       = {32'd0,
                                     msg_rx_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, msg_rx_cntr_dbg_i,
                                     tlp_tx_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, tlp_tx_cntr_dbg_i};
end else begin
   assign pcie_vdm_sts4_dbg       = 64'hBAADBEEF_DEADBEEF; //64'd0;
   assign pcie_vdm_sts5_dbg       = 64'hBAADBEEF_DEADBEEF; //64'd0;
end
endgenerate

endmodule
