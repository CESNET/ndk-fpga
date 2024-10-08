// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// MCTP over PCIe VDM Ingress module is used to parse MCTP over PCIe VDM 
// TLPs and forward the MCTP payloads to MAX10’s MCTP over PCIe VDM buffer.
//-----------------------------------------------------------------------------

module mctp_pcievdm_ingr #(
   parameter   INGR_MSTR_ADDR_WIDTH    = 12,
   parameter   INGR_MSTR_BRST_WIDTH    = 9,
   parameter   DEBUG_REG_EN            = 0,
   parameter   DEBUG_REG_WIDTH         = 8,
   parameter   MCTP_HDR_VERSION        = 4'h1,
   parameter   MCTP_BASELINE_MTU       = 16
)(
   input  logic                            clk,
   input  logic                            reset,
   
   //CSR i/f
   input  logic [7:0]                      pcievdm_mctp_eid,
// input  logic [7:0]                      pcievdm_mctp_mtu_wsize,
   input  logic                            pcievdm_afu_addr_vld,
   output logic [63:0]                     pcie_vdm_sts1_dbg,
   output logic [63:0]                     pcie_vdm_sts2_dbg,
   output logic [63:0]                     pcie_vdm_sts3_dbg,
   input  logic                            pulse_1us,
   
   //Ingress AVMM slave (connected to IOFS-shell/AFU)
   input  logic [0:0]                      avmm_ingr_slv_addr,
   input  logic                            avmm_ingr_slv_write,
   input  logic                            avmm_ingr_slv_read,
   input  logic [63:0]                     avmm_ingr_slv_wrdata,
   input  logic [7:0]                      avmm_ingr_slv_byteen,
   output logic [63:0]                     avmm_ingr_slv_rddata,
   output logic                            avmm_ingr_slv_rddvld,
   output logic                            avmm_ingr_slv_waitreq,

   //Ingress AVMM Master (connected to SPI Master)
   output logic [INGR_MSTR_ADDR_WIDTH-1:0] avmm_ingr_mstr_addr,
   output logic                            avmm_ingr_mstr_write,
   output logic                            avmm_ingr_mstr_read,
   output logic [INGR_MSTR_BRST_WIDTH-1:0] avmm_ingr_mstr_burstcnt,
   output logic [31:0]                     avmm_ingr_mstr_wrdata,
   input  logic [31:0]                     avmm_ingr_mstr_rddata,
   input  logic                            avmm_ingr_mstr_rddvld,
   input  logic                            avmm_ingr_mstr_waitreq
);

localparam  TLP_LEN_WIDTH           = $clog2(MCTP_BASELINE_MTU+1);//TLP length width max
localparam  M10_INGR_CNS_REG_ADDR   = 12'h0;  //M10's Ingress Control and status register address
localparam  M10_INGR_PH_REG_ADDR    = 12'h4;  //M10's Ingress Packet Headre register address
localparam  M10_INGR_PKT_BFR_ADDR   = 12'h800;//M10's Ingress Packet Buffer address
localparam  TX_BUSY_DLY_W           = 4;      //2^4 * 1us = 16us delay

//-----------------------------------------------------------------------------
// Internal Declarations
//-----------------------------------------------------------------------------
enum {
   RX_RESET_BIT   = 0,
   RX_IDLE_BIT    = 1,
   RX_HDR_1_BIT   = 2,
   RX_HDR_2_BIT   = 3,
///RX_HDR_3_BIT   = 4,
   RX_PLOAD_BIT   = 4,
   RX_EOP_BIT     = 5,
   RX_DISCARD_BIT = 6
} rx_state_bit;

enum logic [6:0] {
   RX_RESET_ST    = 7'h1 << RX_RESET_BIT  ,
   RX_IDLE_ST     = 7'h1 << RX_IDLE_BIT   ,
   RX_HDR_1_ST    = 7'h1 << RX_HDR_1_BIT  ,
   RX_HDR_2_ST    = 7'h1 << RX_HDR_2_BIT  ,
///RX_HDR_3_ST    = 7'h1 << RX_HDR_3_BIT  ,
   RX_PLOAD_ST    = 7'h1 << RX_PLOAD_BIT  ,
   RX_EOP_ST      = 7'h1 << RX_EOP_BIT    ,
   RX_DISCARD_ST  = 7'h1 << RX_DISCARD_BIT
} rx_state, rx_next;

enum {
   TX_RESET_BIT      = 0,
   TX_IDLE_BIT       = 1,
   TX_CHK_BUSY_BIT   = 2,
   TX_WR_PLOAD_BIT   = 3,
   TX_WR_HDR_BIT     = 4,
   TX_WR_CTRL_BIT    = 5
} tx_state_bit;

enum logic [5:0] {
   TX_RESET_ST       = 6'h1 << TX_RESET_BIT   ,
   TX_IDLE_ST        = 6'h1 << TX_IDLE_BIT    ,
   TX_CHK_BUSY_ST    = 6'h1 << TX_CHK_BUSY_BIT,
   TX_WR_PLOAD_ST    = 6'h1 << TX_WR_PLOAD_BIT,
   TX_WR_HDR_ST      = 6'h1 << TX_WR_HDR_BIT  ,
   TX_WR_CTRL_ST     = 6'h1 << TX_WR_CTRL_BIT 
} tx_state, tx_next, tx_state_r1;

logic                      ingr_pkt_wr8          ;
logic                      ingr_pkt_wr4          ;
logic                      ingr_pkt_wr8_r1       ;
logic                      flow_ctrl_sop         ;
logic                      flow_ctrl_eop         ;
logic [63:0]               ingr_wrdata_r1        ;
logic                      afu_addr_rdy          ;
logic                      tlp_hdr1_match1       ;
logic                      tlp_hdr1_match2       ;
logic                      tlp_hdr1_match3       ;
logic                      tlp_hdr1_len_ok       ;
logic                      tlp_hdr2_vndrid_match ;
logic [TLP_LEN_WIDTH-1:0]  tlp_payload_len       ;
logic [1:0]                tlp_pad_len           ;
logic [15:0]               tlp_pci_req_id        ;
logic                      tlp_routing           ;
logic                      mctp_hdr_match        ;
logic                      dest_eid_match        ;
logic                      pkt_flag_seq_mis      ;
logic                      multipkt_deid_mis     ;
logic                      multipkt_seid_mis     ;
logic                      multipkt_tag_mis      ;
logic                      multipkt_len_mis      ;
logic                      multipkt_prgrs        ;
logic                      multipkt_drop         ;
logic [7:0]                multipkt_deid         ;
logic [7:0]                multipkt_seid         ;
logic [3:0]                multipkt_tag          ;
logic [TLP_LEN_WIDTH-1:0]  multipkt_len          ;
logic [1:0]                mctp_hdr_pkt_seq      ;
logic [1:0]                mctp_hdr_flag         ;
logic [15:0]               tlp_pci_req_id_latch  ;
logic                      tlp_routing_latch     ;
logic [8:0]                mctp_msg_msb_len      ;
//logic [7:0]                ingr_bfr_last_ofst    ;
logic [1:0]                mctp_msg_lsb_len      ;
logic [1:0]                mctp_deid_latch       ;
logic [7:0]                mctp_seid_latch       ;
logic [3:0]                mctp_tag_latch        ;
logic                      mctp_multipkt         ;
logic [31:0]               ingr_bfr_wrdata       ;
logic                      ingr_bfr_wren         ;
logic [8:0]                ingr_bfr_wrofst       ;
logic                      ingr_bfr_wrpage       ;
logic [7:0]                ingr_bfr_wraddr       ;
logic [31:0]               ingr_bfr_rddata       ;
logic                      ingr_bfr_rddone       ;
logic                      ingr_bfr_rden         ;
logic                      ingr_bfr_rden_r1      ;
logic                      ingr_bfr_rdvld        ;
logic [8:0]                ingr_bfr_rdofst       ;
logic                      ingr_bfr_rdpage       ;
logic [7:0]                ingr_bfr_rdaddr       ;
logic                      dly_busy_rechk        ;
logic [TX_BUSY_DLY_W-1:0]  dly_busy_rechk_cntr   ;
logic                      mctp_pkt_avlbl        ;


//-----------------------------------------------------------------------------
// Ingress AVMM slave logic
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : ingr_avmm
   if(reset) begin
      ingr_pkt_wr8          <= 1'b0;
      ingr_pkt_wr4          <= 1'b0;
      ingr_pkt_wr8_r1       <= 1'b0;
      flow_ctrl_sop         <= 1'b0;
      flow_ctrl_eop         <= 1'b0;
      avmm_ingr_slv_waitreq <= 1'b1;
      avmm_ingr_slv_rddvld  <= 1'b0;
      ingr_wrdata_r1        <= 64'd0;
   end else begin
      if (avmm_ingr_slv_write && !avmm_ingr_slv_waitreq) begin
         flow_ctrl_sop  <= ~avmm_ingr_slv_addr &  avmm_ingr_slv_byteen[0] & avmm_ingr_slv_wrdata[0];
         flow_ctrl_eop  <= ~avmm_ingr_slv_addr &  avmm_ingr_slv_byteen[0] & avmm_ingr_slv_wrdata[1];
         ingr_pkt_wr8   <= (avmm_ingr_slv_addr && avmm_ingr_slv_byteen == 8'hFF) ? 1'b1 : 1'b0;
         ingr_pkt_wr4   <= (avmm_ingr_slv_addr && avmm_ingr_slv_byteen == 8'h0F) ? 1'b1 : 1'b0;
      end else begin
         flow_ctrl_sop <= 1'b0;
         flow_ctrl_eop <= 1'b0;
         ingr_pkt_wr8  <= 1'b0;
         ingr_pkt_wr4  <= 1'b0;
      end 
      
      ingr_pkt_wr8_r1   <= ingr_pkt_wr8 & rx_state[RX_PLOAD_BIT];
      
      if(avmm_ingr_slv_write && !avmm_ingr_slv_waitreq && avmm_ingr_slv_addr)
         ingr_wrdata_r1 <= avmm_ingr_slv_wrdata;
      
      if (avmm_ingr_slv_read && !avmm_ingr_slv_waitreq)
         avmm_ingr_slv_rddvld <= 1'b1;
      else
         avmm_ingr_slv_rddvld <= 1'b0;
         
      if (avmm_ingr_slv_write && !avmm_ingr_slv_waitreq || 
          rx_state[RX_PLOAD_BIT] && tlp_payload_len[TLP_LEN_WIDTH-1:2] == 'd0 &&
                              // (ingr_pkt_wr4 || ingr_pkt_wr8 || ingr_pkt_wr8_r1))
                                                 (ingr_pkt_wr4 || ingr_pkt_wr8))
         avmm_ingr_slv_waitreq <= 1'b1;
      else
         avmm_ingr_slv_waitreq <= 1'b0;
   end
end : ingr_avmm

assign avmm_ingr_slv_rddata = 64'd0;

//-----------------------------------------------------------------------------
// Send (or decide to send) discovery notification request when card is ready
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : ss_addr_chk
   if(reset) begin
      afu_addr_rdy   <= 1'b0;
   end else if(tx_state[TX_WR_CTRL_BIT] && !mctp_pkt_avlbl) begin
      afu_addr_rdy   <= pcievdm_afu_addr_vld;
   end
end : ss_addr_chk


//-----------------------------------------------------------------------------
// Ingress PCIe VDM TLP receiving and parsing FSM.
// This FSM receives the TLP from AFU and parses it and stores the MCTP payload
// in ingress buffer.
// Top "always_ff" simply switches the state of the state machine registers.
// Following "always_comb" contains all of the next-state decoding logic.
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : rx_fsm_seq
   if (reset)
      rx_state <= RX_RESET_ST;
//   else if (flow_ctrl_sop)
//      rx_state <= RX_HDR_1_ST;
   else
      rx_state <= rx_next;
end : rx_fsm_seq

always_comb
begin : rx_fsm_comb
   rx_next = rx_state;
   unique case (1'b1) //Reverse Case Statement
      rx_state[RX_RESET_BIT]:   //RX_RESET_ST
         if (reset)
            rx_next = RX_RESET_ST;
         else
            rx_next = RX_IDLE_ST;
      
      rx_state[RX_IDLE_BIT]:   //RX_IDLE_ST
         if (flow_ctrl_sop && ingr_bfr_wrpage == ingr_bfr_rdpage)
            rx_next = RX_HDR_1_ST;
      
      rx_state[RX_HDR_1_BIT]:   //RX_HDR_1_ST
         if(ingr_bfr_wrpage != ingr_bfr_rdpage || ingr_pkt_wr8 && 
           (!tlp_hdr1_match1 || !tlp_hdr1_match2 || !tlp_hdr1_match3 || !tlp_hdr1_len_ok))
            rx_next = RX_IDLE_ST;
         else if(ingr_pkt_wr8)
            rx_next = RX_HDR_2_ST;
      
      rx_state[RX_HDR_2_BIT]:   //RX_HDR_2_ST
         if (flow_ctrl_sop)
            rx_next = RX_HDR_1_ST;
         else if(ingr_pkt_wr8 && !tlp_hdr2_vndrid_match)
            rx_next = RX_IDLE_ST;
         else if(ingr_pkt_wr8) begin 
            if(mctp_hdr_match && dest_eid_match &&      
               !pkt_flag_seq_mis && !multipkt_deid_mis && !multipkt_seid_mis && 
               !multipkt_tag_mis && !multipkt_len_mis)
               rx_next = RX_PLOAD_ST;
            else
               rx_next = RX_DISCARD_ST;
         end
      
      rx_state[RX_PLOAD_BIT]:   //RX_PLOAD_ST
         if (flow_ctrl_sop)
            rx_next = RX_HDR_1_ST;
         else if (flow_ctrl_eop || ingr_bfr_wrofst[8])
            rx_next = RX_DISCARD_ST;
         else if (tlp_payload_len == 'd0 || tlp_payload_len == 'd1 && ingr_pkt_wr4)
            rx_next = RX_EOP_ST;
      
      rx_state[RX_EOP_BIT]:   //RX_EOP_ST
         if (flow_ctrl_sop)
            rx_next = RX_HDR_1_ST;
         else if(flow_ctrl_eop) //End of pkt condition : MCTP pkt is valid here
            rx_next = RX_IDLE_ST;
         else if(ingr_pkt_wr8 || ingr_pkt_wr4)
            rx_next = RX_DISCARD_ST;
      
      rx_state[RX_DISCARD_BIT]:   //RX_DISCARD_ST
         if (flow_ctrl_sop)
            rx_next = RX_HDR_1_ST;
         else 
            rx_next = RX_IDLE_ST;
   endcase
end : rx_fsm_comb


//-----------------------------------------------------------------------------
// TLP header parsing logic.
// PCI Target ID is checked by PCIe HIP and no need to check here.
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : tlp_hdr_parse
   if (reset) begin
      tlp_hdr1_match1       <= 1'b0;
      tlp_hdr1_match2       <= 1'b0;
      tlp_hdr1_match3       <= 1'b0;
      tlp_hdr1_len_ok       <= 1'b0;
      tlp_hdr2_vndrid_match <= 1'b0;
      tlp_payload_len       <= {TLP_LEN_WIDTH{1'b0}};
      tlp_pad_len           <= 2'd0;
      tlp_pci_req_id        <= 16'd0;
      tlp_routing           <= 1'b0;
   end else begin
      if(avmm_ingr_slv_wrdata[7:3] == 5'h0E &&    //R/Fmt == 3'b011 && Type[4:3] == 2'b10
         (avmm_ingr_slv_wrdata[2:0] == 3'b010 ||  //Type[2:0] == 3'b010 (Route by ID)
       // avmm_ingr_slv_wrdata[2:0] == 3'b000 ||  //Type[2:0] == 3'b000 (route to RC)
          avmm_ingr_slv_wrdata[2:0] == 3'b011) && //Type[2:0] == 3'b011 (Broadcast from RC)
         avmm_ingr_slv_wrdata[15:14] == 2'b0)     //R/T9 == 1'b0 && TC[2] == 1'b0 
         tlp_hdr1_match1 <= 1'b1;
      else
         tlp_hdr1_match1 <= 1'b0;
      
      if(avmm_ingr_slv_wrdata[13:8] == 6'h00 &&    //TC[1:0] == 2'b00 && T8/Attr/LN/TH == 4'h0 
         //avmm_ingr_slv_wrdata[23] can be anything
         avmm_ingr_slv_wrdata[22] == 1'b0 &&       //EP == 1'b0
         (avmm_ingr_slv_wrdata[21:20] == 2'b00 ||  //Attr == 2'b00 or 2'b01
          avmm_ingr_slv_wrdata[21:20] == 2'b01) && //Attr == 2'b00 or 2'b01
         avmm_ingr_slv_wrdata[19:18] == 2'b00)     //R/AT == 2'b00
         tlp_hdr1_match2 <= 1'b1;
      else 
         tlp_hdr1_match2 <= 1'b0;
      
      if(avmm_ingr_slv_wrdata[51:48] == 4'h0 && //MCTP VDM code == 4'h0
         avmm_ingr_slv_wrdata[63:56] == 8'h7F)  //Message Code Vendor Defined == 8'h7F
         tlp_hdr1_match3 <= 1'b1;
      else 
         tlp_hdr1_match3 <= 1'b0;
      
      //Length should be a non-zero value which is less than or equal to Baseline MTU size
      if(avmm_ingr_slv_wrdata[17:16] == 2'h0 &&
         avmm_ingr_slv_wrdata[31:24] != 8'h0 && 
         avmm_ingr_slv_wrdata[31:24] <= MCTP_BASELINE_MTU)
         tlp_hdr1_len_ok <= 1'b1;
      else 
         tlp_hdr1_len_ok <= 1'b0;
      
      if(avmm_ingr_slv_wrdata[23:16] == 8'h1A && avmm_ingr_slv_wrdata[31:24] == 8'hB4)  //Vendor ID == 16'h1AB4(DMTF)
         tlp_hdr2_vndrid_match <= 1'b1;
      else
         tlp_hdr2_vndrid_match <= 1'b0;

      //Latch TLP Header-1 parameters
      if(rx_state[RX_HDR_1_BIT] && ingr_pkt_wr8) begin
         tlp_payload_len <= ingr_wrdata_r1[24+:TLP_LEN_WIDTH];
         tlp_pad_len     <= ingr_wrdata_r1[53:52];
         tlp_pci_req_id  <= {ingr_wrdata_r1[39:32], ingr_wrdata_r1[47:40]};
         tlp_routing     <= ~ingr_wrdata_r1[0];
      end else if(rx_state[RX_PLOAD_BIT] && ingr_pkt_wr8)
         tlp_payload_len <= tlp_payload_len - 2'd2;
         
   end
end : tlp_hdr_parse


//-----------------------------------------------------------------------------
// MCTP header parsing logic.
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : mctp_hdr_parse
   if (reset) begin
      mctp_hdr_match        <= 1'b0;
      dest_eid_match        <= 1'b0;
      pkt_flag_seq_mis      <= 1'b0;
      multipkt_deid_mis     <= 1'b0;
      multipkt_seid_mis     <= 1'b0;
      multipkt_tag_mis      <= 1'b0;
      multipkt_len_mis      <= 1'b0;
      multipkt_prgrs        <= 1'b0;
      multipkt_drop         <= 1'b0;
      multipkt_deid         <= 8'd0;
      multipkt_seid         <= 8'd0;
      multipkt_tag          <= 4'd0;
      multipkt_len          <= {TLP_LEN_WIDTH{1'b0}};
      mctp_hdr_pkt_seq      <= 2'd0;
      mctp_hdr_flag         <= 2'd0;
   end else begin
      if(//avmm_ingr_slv_wrdata[31:28] == 4'h0 &&           //MCTP header reserved
         avmm_ingr_slv_wrdata[35:32] == MCTP_HDR_VERSION) //MCTP header version
         mctp_hdr_match <= 1'b1;
      else 
         mctp_hdr_match <= 1'b0;
      
      if(avmm_ingr_slv_wrdata[47:40] == pcievdm_mctp_eid || //Our EID
         avmm_ingr_slv_wrdata[47:40] == 8'h00 ||            //Null EID
         avmm_ingr_slv_wrdata[47:40] == 8'hFF)              //Broadcast EID
         dest_eid_match <= 1'b1;
      else 
         dest_eid_match <= 1'b0;
      
      //Latch multipacket flag if SOM = 1 & EOM = 0; deassert when EOM = 1
      if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && ingr_wrdata_r1[62])
         multipkt_prgrs <= 1'b0;
      else if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && ingr_wrdata_r1[63])
         multipkt_prgrs <= 1'b1;
      
      //Multipacket message dropped indication
      if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && ingr_wrdata_r1[63]) // || !multipkt_prgrs)
         multipkt_drop <= 1'b0;
      else if(multipkt_prgrs && rx_state[RX_DISCARD_BIT])
         multipkt_drop <= 1'b1;
      
      //Latch MCTP header parameters for first packet of multipacket
      if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && ingr_wrdata_r1[63]) begin
         multipkt_deid <= ingr_wrdata_r1[47:40];
         multipkt_seid <= ingr_wrdata_r1[55:48];
         multipkt_tag  <= ingr_wrdata_r1[59:56];
         multipkt_len  <= tlp_payload_len;
      end
      
      //Multipacket Dest EID miss for middle and last packets
      if(!avmm_ingr_slv_wrdata[63] && multipkt_deid != avmm_ingr_slv_wrdata[47:40])
         multipkt_deid_mis <= 1'b1;
      else 
         multipkt_deid_mis <= 1'b0;
      
      //Multipacket Source EID miss for middle and last packets      
      if(!avmm_ingr_slv_wrdata[63] && multipkt_seid != avmm_ingr_slv_wrdata[55:48])
         multipkt_seid_mis <= 1'b1;
      else
         multipkt_seid_mis <= 1'b0;
      
      //Multipacket Tag miss for middle and last packets
      if(!avmm_ingr_slv_wrdata[63] && multipkt_tag  != avmm_ingr_slv_wrdata[59:56])
         multipkt_tag_mis  <= 1'b1;
      else
         multipkt_tag_mis  <= 1'b0;
      
      //In multipacket sequence, middle pkt length should be same as that of first pkt
      //last pkt length should be less than or equal to first pkt length
      //middle packets should not have padding bytes (i.e. DWORD aligned)
      if(!avmm_ingr_slv_wrdata[63] && (
         !avmm_ingr_slv_wrdata[62] && tlp_payload_len != multipkt_len ||
          avmm_ingr_slv_wrdata[62] && tlp_payload_len >  multipkt_len ||
         !avmm_ingr_slv_wrdata[62] && tlp_pad_len != 2'd0))
         multipkt_len_mis  <= 1'b1;
      else 
         multipkt_len_mis  <= 1'b0;
      
      //Latch packet sequence and flags
      if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && tlp_hdr2_vndrid_match) begin 
         mctp_hdr_flag  <= ingr_wrdata_r1[63:62];
         
         if(ingr_wrdata_r1[63])
            mctp_hdr_pkt_seq <= ingr_wrdata_r1[61:60] + 1'b1;
         else
            mctp_hdr_pkt_seq <= mctp_hdr_pkt_seq + 1'b1;
      end
      
      //Flag or packet sequence error when
      //    1) Unexpected middle/last packets when not in mutlipacket sequence
      //    2) Multipacket packet sequencer is not modulo 4 increment value
      //    3) Multipacket middle/last drop due to previous drops of packet in the same sequence
      // if(rx_state[RX_HDR_2_BIT] && avmm_ingr_slv_write && 
      if(!avmm_ingr_slv_wrdata[63] && (!multipkt_prgrs || multipkt_drop ||
          multipkt_prgrs && mctp_hdr_pkt_seq != avmm_ingr_slv_wrdata[61:60]))
         pkt_flag_seq_mis <= 1'b1;
      else
         pkt_flag_seq_mis <= 1'b0;
   end
end : mctp_hdr_parse


//-----------------------------------------------------------------------------
// Latch PCIe TLP and MCTP params for M10 Nios FW
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : ingr_param_latch
   if (reset) begin
      tlp_pci_req_id_latch <= 16'd0;
      tlp_routing_latch    <= 1'b0;
      mctp_msg_msb_len     <= 9'd0;
      mctp_msg_lsb_len     <= 2'd0;
      mctp_deid_latch      <= 2'd0;
      mctp_seid_latch      <= 8'd0;
      mctp_tag_latch       <= 4'd0;
      mctp_multipkt        <= 1'b0;
   end else begin
      if(rx_state[RX_EOP_BIT] && flow_ctrl_eop) begin
         if(mctp_hdr_flag[1]) begin
            tlp_pci_req_id_latch <= tlp_pci_req_id;
            tlp_routing_latch    <= tlp_routing;
         end
         if(mctp_hdr_flag[0]) begin
            mctp_msg_msb_len     <= ingr_bfr_wrofst; // - 1'b1;
            mctp_msg_lsb_len     <= tlp_pad_len;
            mctp_deid_latch      <= (multipkt_deid == 8'h00) ? 2'd0 : 
                                    (multipkt_deid == 8'hFF) ? 2'd1 : 2'd2;
            mctp_seid_latch      <= multipkt_seid;
            mctp_tag_latch       <= multipkt_tag;
         end
         mctp_multipkt           <= (mctp_hdr_flag == 2'd1) ? 1'b1 : 1'b0;
      end
   end
end : ingr_param_latch 


//-----------------------------------------------------------------------------
// Ingress Buffer Write Logic
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : ingr_bfr_wr
   if (reset) begin
      ingr_bfr_wrdata      <= 32'd0;
      ingr_bfr_wren        <= 1'b0;
      ingr_bfr_wrofst      <= 9'd0;
      ingr_bfr_wrpage      <= 1'b0;
   end else begin
      if(ingr_pkt_wr8 || ingr_pkt_wr4)
         ingr_bfr_wrdata   <= ingr_wrdata_r1[31:0];
      else if(ingr_pkt_wr8_r1)
         ingr_bfr_wrdata   <= ingr_wrdata_r1[63:32];
         
      if(rx_state[RX_PLOAD_BIT] && (ingr_pkt_wr8 || ingr_pkt_wr4 || ingr_pkt_wr8_r1))
         ingr_bfr_wren     <= 1'b1;
      else
         ingr_bfr_wren     <= 1'b0;
        
      //Reset buffer write offset for every packet with SOM=1
      if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && ingr_wrdata_r1[63])
         ingr_bfr_wrofst   <= 9'd0;
      else if(ingr_bfr_wren)
         ingr_bfr_wrofst   <= ingr_bfr_wrofst + 1'b1;
      
      //Flip page to indicate message receive successfull (once per pkt @ EOM=1)
      if(rx_state[RX_EOP_BIT] && flow_ctrl_eop && mctp_hdr_flag[0] && 
                                                  ingr_bfr_wrofst <= 9'd256)
         ingr_bfr_wrpage     <= ~ingr_bfr_wrpage;
   end
end : ingr_bfr_wr

assign ingr_bfr_wraddr = ingr_bfr_wrofst[7:0];


//-----------------------------------------------------------------------------
// Ingress Buffer Instantiation
//-----------------------------------------------------------------------------
altera_syncram ingress_buffer 
(
   .clock0           (clk              ),
   .address_a        (ingr_bfr_wraddr  ),
   .address_b        (ingr_bfr_rdaddr  ),
   .data_a           (ingr_bfr_wrdata  ),
   .wren_a           (ingr_bfr_wren    ),
   .q_b              (ingr_bfr_rddata  ),
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
   ingress_buffer.address_aclr_b          = "NONE",
   ingress_buffer.address_reg_b           = "CLOCK0",
   ingress_buffer.clock_enable_input_a    = "BYPASS",
   ingress_buffer.clock_enable_input_b    = "BYPASS",
   ingress_buffer.clock_enable_output_b   = "BYPASS",
   ingress_buffer.intended_device_family  = "Agilex",
   ingress_buffer.lpm_type                = "altera_syncram",
   ingress_buffer.numwords_a              = 256,
   ingress_buffer.numwords_b              = 256,
   ingress_buffer.operation_mode          = "DUAL_PORT",
   ingress_buffer.outdata_aclr_b          = "NONE",
   ingress_buffer.outdata_sclr_b          = "NONE",
   ingress_buffer.outdata_reg_b           = "CLOCK0",
   ingress_buffer.power_up_uninitialized  = "FALSE",
   ingress_buffer.read_during_write_mode_mixed_ports  = "DONT_CARE",
   ingress_buffer.widthad_a               = 8,
   ingress_buffer.widthad_b               = 8,
   ingress_buffer.width_a                 = 32,
   ingress_buffer.width_b                 = 32,
   ingress_buffer.width_byteena_a         = 1;


//-----------------------------------------------------------------------------
// Ingress MCTP payload transmit FSM.
// This FSM reads the MCTP payload stored in ingress buffer and transmits
// or pushes it to MAX10's MCTP over PCIe VDM buffer.
// Top "always_ff" simply switches the state of the state machine registers.
// Following "always_comb" contains all of the next-state decoding logic.
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : tx_fsm_seq
   if (reset) begin
      tx_state    <= TX_RESET_ST;
      tx_state_r1 <= TX_RESET_ST;
   end else begin
      tx_state    <= tx_next;
      tx_state_r1 <= tx_state;
   end   
end : tx_fsm_seq

always_comb
begin : tx_fsm_comb
   tx_next = tx_state;
   unique case (1'b1) //Reverse Case Statement
      tx_state[TX_RESET_BIT]:   //TX_RESET_ST
         if (reset)
            tx_next = TX_RESET_ST;
         else
            tx_next = TX_IDLE_ST;
      
      tx_state[TX_IDLE_BIT]:   //TX_IDLE_ST
         if(!afu_addr_rdy && pcievdm_afu_addr_vld)
            tx_next = TX_WR_CTRL_ST;
         else if (ingr_bfr_wrpage != ingr_bfr_rdpage)
            tx_next = TX_CHK_BUSY_ST;
      
      tx_state[TX_CHK_BUSY_BIT]:   //TX_CHK_BUSY_ST
         if(avmm_ingr_mstr_rddvld && !avmm_ingr_mstr_rddata[4])
            tx_next = TX_WR_PLOAD_ST;
            
      tx_state[TX_WR_PLOAD_BIT]:   //TX_WR_PLOAD_ST
         // if(ingr_bfr_rdofst == ingr_bfr_last_ofst) // && !avmm_ingr_mstr_waitreq && avmm_ingr_mstr_write)
         if(ingr_bfr_rddone && !avmm_ingr_mstr_waitreq && avmm_ingr_mstr_write)
            tx_next = TX_WR_HDR_ST;

      tx_state[TX_WR_HDR_BIT]:   //TX_WR_HDR_ST  
         if(!avmm_ingr_mstr_waitreq && avmm_ingr_mstr_write)
            tx_next = TX_WR_CTRL_ST;

      tx_state[TX_WR_CTRL_BIT]:   //TX_WR_CTRL_ST 
         if(!avmm_ingr_mstr_waitreq && avmm_ingr_mstr_write)
            tx_next = TX_IDLE_ST;
   endcase
end : tx_fsm_comb


//-----------------------------------------------------------------------------
// Ingress Buffer Read Logic
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : ingr_bfr_rd
   if (reset) begin
      ingr_bfr_rddone      <= 1'b0;
      ingr_bfr_rden        <= 1'b0;
      ingr_bfr_rden_r1     <= 1'b0;
      ingr_bfr_rdvld       <= 1'b0;
      ingr_bfr_rdofst      <= 9'd0;
      ingr_bfr_rdpage      <= 1'b0;
      //ingr_bfr_last_ofst   <= 8'd0;
   end else begin
      //ingr_bfr_last_ofst   <= mctp_msg_msb_len - 1'b1;

      //if(tx_state[TX_WR_PLOAD_BIT] && ingr_bfr_rdofst != ingr_bfr_last_ofst && 
      //                     !avmm_ingr_mstr_waitreq && avmm_ingr_mstr_write) // && !ingr_bfr_rddone)
      if(ingr_bfr_rdofst == (mctp_msg_msb_len - 1'b1))
         ingr_bfr_rddone   <= 1'b1;
      else 
         ingr_bfr_rddone   <= 1'b0;
      
      if(!tx_state[TX_WR_PLOAD_BIT])
         ingr_bfr_rdofst   <= 9'd0;
      else if(!ingr_bfr_rddone && !avmm_ingr_mstr_waitreq && avmm_ingr_mstr_write)
         ingr_bfr_rdofst   <= ingr_bfr_rdofst + 1'b1;
      
      if(!ingr_bfr_rddone & ~avmm_ingr_mstr_waitreq & avmm_ingr_mstr_write)
         ingr_bfr_rden     <= 1'b1;
      else
         ingr_bfr_rden     <= 1'b0;
      
      ingr_bfr_rden_r1     <= ingr_bfr_rden;
      
      //Flip page to indicate message read from ingress buffer
      if(tx_state[TX_WR_CTRL_BIT] && mctp_pkt_avlbl && 
                                !avmm_ingr_mstr_waitreq && avmm_ingr_mstr_write)
         ingr_bfr_rdpage   <= ~ingr_bfr_rdpage;
      
      if(tx_state[TX_WR_PLOAD_BIT] && (!tx_state_r1[TX_WR_PLOAD_BIT] || ingr_bfr_rden_r1))
         ingr_bfr_rdvld    <= 1'b1;
      else 
         ingr_bfr_rdvld    <= 1'b0;
   end
end : ingr_bfr_rd

assign ingr_bfr_rdaddr = ingr_bfr_rdofst[7:0];


//-----------------------------------------------------------------------------
// Ingress (tx) AVMM master signal generation
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : ingr_tx_avmm
   if (reset) begin
      avmm_ingr_mstr_addr     <= {INGR_MSTR_ADDR_WIDTH{1'b0}};
      avmm_ingr_mstr_write    <= 1'b0;
      avmm_ingr_mstr_read     <= 1'b0;
      avmm_ingr_mstr_burstcnt <= {INGR_MSTR_BRST_WIDTH{1'b0}};
      avmm_ingr_mstr_wrdata   <= 32'd0;
      dly_busy_rechk          <= 1'b0;
      dly_busy_rechk_cntr     <= {TX_BUSY_DLY_W{1'b0}};
      mctp_pkt_avlbl          <= 1'b0;
   end else begin
      if(tx_state[TX_WR_PLOAD_BIT] && ingr_bfr_rdvld || 
         tx_state[TX_WR_HDR_BIT]   && !tx_state_r1[TX_WR_HDR_BIT] ||
         tx_state[TX_WR_CTRL_BIT]  && !tx_state_r1[TX_WR_CTRL_BIT])
         avmm_ingr_mstr_write <= 1'b1;
      else if(!avmm_ingr_mstr_waitreq)
         avmm_ingr_mstr_write <= 1'b0;
      
      if(!tx_state[TX_CHK_BUSY_BIT] || avmm_ingr_mstr_read)
         dly_busy_rechk <= 1'b0;
      else if(avmm_ingr_mstr_rddvld && avmm_ingr_mstr_rddata[4])
         dly_busy_rechk <= 1'b1;
      
      if(!dly_busy_rechk)
         dly_busy_rechk_cntr <= {TX_BUSY_DLY_W{1'b0}};
      else if(pulse_1us)
         dly_busy_rechk_cntr <= dly_busy_rechk_cntr - 1'b1;
      
      if(tx_state[TX_CHK_BUSY_BIT] && !tx_state_r1[TX_CHK_BUSY_BIT] ||
         //avmm_ingr_mstr_rddvld && !avmm_ingr_mstr_rddata[4]) //no delay
         dly_busy_rechk && dly_busy_rechk_cntr == 'd1 && pulse_1us)
         avmm_ingr_mstr_read  <= 1'b1;
      else if(!avmm_ingr_mstr_waitreq)
         avmm_ingr_mstr_read  <= 1'b0;
      
      if(tx_state[TX_WR_PLOAD_BIT])
         avmm_ingr_mstr_addr  <= M10_INGR_PKT_BFR_ADDR;
      else if(tx_state[TX_WR_HDR_BIT])
         avmm_ingr_mstr_addr  <= M10_INGR_PH_REG_ADDR;
      else 
         avmm_ingr_mstr_addr  <= M10_INGR_CNS_REG_ADDR;
      
      if(tx_state[TX_WR_PLOAD_BIT])
         avmm_ingr_mstr_burstcnt  <= mctp_msg_msb_len;
      else 
         avmm_ingr_mstr_burstcnt  <= 'd1;
      
      if(tx_state[TX_WR_HDR_BIT])
         mctp_pkt_avlbl <= 1'b1;
      else if(!tx_state[TX_WR_CTRL_BIT])
         mctp_pkt_avlbl <= 1'b0;
      
      if(tx_state[TX_WR_PLOAD_BIT])
         avmm_ingr_mstr_wrdata <= ingr_bfr_rddata;
      else if(tx_state[TX_WR_HDR_BIT])
         avmm_ingr_mstr_wrdata <= {mctp_deid_latch,      //[31:30] Dest EID
                                   tlp_routing_latch,    //[29]	 PCIe TLP route 
                                   mctp_multipkt,        //[28]	 Multipacket message
                                   mctp_tag_latch,       //[27:24] {TO_bit, Message_tag}
                                   mctp_seid_latch,      //[23:8]  Source EID
                                   tlp_pci_req_id_latch};//[15:0]  PCIe Req ID
      else 
         avmm_ingr_mstr_wrdata <= {12'd0,           //[31:20] Reserved
                                   1'd0, mctp_msg_msb_len, mctp_msg_lsb_len, //[19:8]  Rx packet size
                                   3'd0,            //[7:3]   Reserved
                                   1'd0,            //[4]     M10 Nios busy
                                   2'd0,            //[3:2]   Reserved
                                   ~mctp_pkt_avlbl, //[1]     PCIe BDF init done
                                   mctp_pkt_avlbl}; //[0]     Rx packet available
   end
end : ingr_tx_avmm


//-----------------------------------------------------------------------------
// Debug registers
//-----------------------------------------------------------------------------
generate 
if (DEBUG_REG_EN == 1) begin
   logic [DEBUG_REG_WIDTH-2:0] tlp_rcvd_cntr_dbg_i    ;
   logic                       tlp_rcvd_of_dbg_i      ;
   logic                       b2b_drop_dbg_i         ;
   logic [DEBUG_REG_WIDTH-2:0] b2b_drop_cntr_dbg_i    ;
   logic                       b2b_drop_of_dbg_i      ;
   logic                       tlp_hdr_mis_dbg_i      ;
   logic [DEBUG_REG_WIDTH-2:0] tlp_hdr_mis_cntr_dbg_i ;
   logic                       tlp_hdr_mis_of_dbg_i   ;
   logic [DEBUG_REG_WIDTH-2:0] mctp_hdr_mis_cntr_dbg_i;
   logic                       mctp_hdr_mis_of_dbg_i  ;
   logic                       multipkt_mis_dbg_i     ;
   logic [DEBUG_REG_WIDTH-2:0] multipkt_mis_cntr_dbg_i;
   logic                       multipkt_mis_of_dbg_i  ;
   logic                       ingr_bfr_wrpage_r1     ;
   logic [DEBUG_REG_WIDTH-2:0] vld_msg_rx_cntr_dbg_i  ;
   logic                       vld_msg_rx_of_dbg_i    ;
   logic                       ingr_bfr_rdpage_r1     ;
   logic [DEBUG_REG_WIDTH-2:0] vld_msg_tx_cntr_dbg_i  ;
   logic                       vld_msg_tx_of_dbg_i    ;
   
   always_ff @(posedge clk, posedge reset)
   begin : dbg_reg
      if (reset) begin
         tlp_rcvd_cntr_dbg_i     <= 'd0;
         tlp_rcvd_of_dbg_i       <= 1'b0;
         b2b_drop_dbg_i          <= 1'b0;
         b2b_drop_cntr_dbg_i     <= 'd0;
         b2b_drop_of_dbg_i       <= 1'b0;
         tlp_hdr_mis_dbg_i       <= 1'b0;
         tlp_hdr_mis_cntr_dbg_i  <= 'd0;
         tlp_hdr_mis_of_dbg_i    <= 1'b0;
         mctp_hdr_mis_cntr_dbg_i <= 'd0;
         mctp_hdr_mis_of_dbg_i   <= 1'b0;
         multipkt_mis_dbg_i      <= 1'b0;
         multipkt_mis_cntr_dbg_i <= 'd0;
         multipkt_mis_of_dbg_i   <= 1'b0;
         ingr_bfr_wrpage_r1      <= 1'b0;
         vld_msg_rx_cntr_dbg_i   <= 'd0;
         vld_msg_rx_of_dbg_i     <= 1'b0;
         ingr_bfr_rdpage_r1      <= 1'b0;
         vld_msg_tx_cntr_dbg_i   <= 'd0;
         vld_msg_tx_of_dbg_i     <= 1'b0;
      end else begin
         //Total number of VDM TLP's received
         if(flow_ctrl_eop)
            tlp_rcvd_cntr_dbg_i <= tlp_rcvd_cntr_dbg_i + 1'b1;
         
         if(flow_ctrl_eop && (&tlp_rcvd_cntr_dbg_i))
            tlp_rcvd_of_dbg_i   <= 1'b1;
         
         //Total number of TLP's due to receiver (i.e. this module) busy
         if(rx_state[RX_IDLE_BIT] && flow_ctrl_sop && 
                                          ingr_bfr_wrpage != ingr_bfr_rdpage ||
            rx_state[RX_HDR_1_BIT] && ingr_bfr_wrpage != ingr_bfr_rdpage)
            b2b_drop_dbg_i <= 1'b1;
         else
            b2b_drop_dbg_i <= 1'b0;
         
         if(b2b_drop_dbg_i)
            b2b_drop_cntr_dbg_i <= b2b_drop_cntr_dbg_i + 1'b1;
         
         if(b2b_drop_dbg_i && (&b2b_drop_cntr_dbg_i))
            b2b_drop_of_dbg_i   <= 1'b1;
         
         //Number of TLP's received with TLP header mismatch
         if(rx_state[RX_HDR_1_BIT] && ingr_pkt_wr8 &&  (!tlp_hdr1_match1 || 
               !tlp_hdr1_match2 || !tlp_hdr1_match3 || !tlp_hdr1_len_ok) ||
            rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && !tlp_hdr2_vndrid_match)
            tlp_hdr_mis_dbg_i   <= 1'b1;
         else
            tlp_hdr_mis_dbg_i   <= 1'b0;
            
         if(tlp_hdr_mis_dbg_i)
            tlp_hdr_mis_cntr_dbg_i <= tlp_hdr_mis_cntr_dbg_i + 1'b1;
         
         if(tlp_hdr_mis_dbg_i && (&tlp_hdr_mis_cntr_dbg_i))
            tlp_hdr_mis_of_dbg_i <= 1'b1;
         
         //Number of TLP's received with MCTP header version or Destination EID 
         //or MCTP header flag/seq mismatch
         if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && 
                                           (!mctp_hdr_match || !dest_eid_match))
            mctp_hdr_mis_cntr_dbg_i <= mctp_hdr_mis_cntr_dbg_i + 1'b1;
         
         if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && (&mctp_hdr_mis_cntr_dbg_i) &&  
                                          (!mctp_hdr_match || !dest_eid_match))
            mctp_hdr_mis_of_dbg_i <= 1'b1;
         
         //Number of TLP's received with multipacket error
         if(rx_state[RX_HDR_2_BIT] && ingr_pkt_wr8 && (pkt_flag_seq_mis || multipkt_deid_mis ||
                     multipkt_seid_mis || multipkt_tag_mis || multipkt_len_mis))
            multipkt_mis_dbg_i <= 1'b1;
         else 
            multipkt_mis_dbg_i <= 1'b0;
            
         if(multipkt_mis_dbg_i)
            multipkt_mis_cntr_dbg_i <= multipkt_mis_cntr_dbg_i + 1'b1;

         if(multipkt_mis_dbg_i && (&multipkt_mis_cntr_dbg_i))
            multipkt_mis_of_dbg_i <= 1'b1;
         
         //Number of valid MCTP messages received
         ingr_bfr_wrpage_r1   <= ingr_bfr_wrpage;
         if(ingr_bfr_wrpage != ingr_bfr_wrpage_r1)
            vld_msg_rx_cntr_dbg_i <= vld_msg_rx_cntr_dbg_i + 1'b1;

         if(ingr_bfr_wrpage != ingr_bfr_wrpage_r1 && (&vld_msg_rx_cntr_dbg_i))
            vld_msg_rx_of_dbg_i <= 1'b1;
         
         //Number of valid MCTP messages received
         ingr_bfr_rdpage_r1   <= ingr_bfr_rdpage;
         if(ingr_bfr_rdpage_r1 != ingr_bfr_rdpage)
            vld_msg_tx_cntr_dbg_i <= vld_msg_tx_cntr_dbg_i + 1'b1;

         if(ingr_bfr_rdpage_r1 != ingr_bfr_rdpage && (&vld_msg_tx_cntr_dbg_i))
            vld_msg_tx_of_dbg_i <= 1'b1;
      end
   end : dbg_reg
   
   assign pcie_vdm_sts1_dbg       = {49'd0,
                                     ingr_bfr_rdpage, //[14]   - Ingress read page
                                     tx_state,        //[13:8] - Ingress transmitter FSM state
                                     ingr_bfr_wrpage, //[7]    - Ingress write page
                                     rx_state};       //[6:0]  - Ingress receiver FSM state
   
   //[63:48] - Total number of TLPs received counter
   //[47:32] - Back to back message drop counter
   //[31:16] - TLP header mismatch counter
   //[15:0]  - MCTP header mismatch counter
   assign pcie_vdm_sts2_dbg       = {tlp_rcvd_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, tlp_rcvd_cntr_dbg_i,         
                                     b2b_drop_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, b2b_drop_cntr_dbg_i,         
                                     tlp_hdr_mis_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, tlp_hdr_mis_cntr_dbg_i,   
                                     mctp_hdr_mis_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, mctp_hdr_mis_cntr_dbg_i};
                                     
   //[63:48] - Reserved
   //[47:32] - Multipacket error counter
   //[31:16] - Valid MCTP messages received counter
   //[15:0]  - MCTP messages transmitter counter
   assign pcie_vdm_sts3_dbg       = {16'd0,
                                     multipkt_mis_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, multipkt_mis_cntr_dbg_i,
                                     vld_msg_rx_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, vld_msg_rx_cntr_dbg_i,
                                     vld_msg_tx_of_dbg_i, {(16-DEBUG_REG_WIDTH){1'b0}}, vld_msg_tx_cntr_dbg_i};
end else begin
   assign pcie_vdm_sts1_dbg       = 64'hBAADBEEF_DEADBEEF; //64'd0;
   assign pcie_vdm_sts2_dbg       = 64'hBAADBEEF_DEADBEEF; //64'd0;
   assign pcie_vdm_sts3_dbg       = 64'hBAADBEEF_DEADBEEF; //64'd0;
end
endgenerate

endmodule
