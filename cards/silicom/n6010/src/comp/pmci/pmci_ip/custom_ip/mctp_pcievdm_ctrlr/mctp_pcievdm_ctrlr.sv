// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// MCTP over PCIe VDM Controller module is used to parse MCTP over PCIe VDM 
// TLPs and forward the MCTP payloads to MAX10’s MCTP over PCIe VDM buffer.
// Similarlly in the other direction, this module receives the MCTP payload 
// from MAX10’s MCTP over PCIe VDM buffer and constructs PCIe VDM TLPs and 
// forwards it.
//-----------------------------------------------------------------------------

module mctp_pcievdm_ctrlr #(
   parameter   INGR_MSTR_ADDR_WIDTH     = 12,
   parameter   INGR_MSTR_BRST_WIDTH     = 9,
   parameter   EGRS_SLV_ADDR_WIDTH      = 9,
   parameter   SS_ADDR_WIDTH            = 21,
   parameter   MCTP_BASELINE_MTU        = 16,  //in DWORDs, i.e. 64/4 = 16 (should be aligned to 64bits)
   parameter   DEBUG_REG_EN             = 0,
   parameter   DEBUG_REG_WIDTH          = 8
   
)(
   input  logic                            clk,
   input  logic                            reset,
   
   //CSR i/f
   input  logic [SS_ADDR_WIDTH-1:0]        pcievdm_afu_addr,
   input  logic                            pcievdm_afu_addr_vld,
   input  logic [7:0]                      pcievdm_mctp_eid,
   output logic [63:0]                     pcie_vdm_sts1_dbg,
   output logic [63:0]                     pcie_vdm_sts2_dbg,
   output logic [63:0]                     pcie_vdm_sts3_dbg,
   output logic [63:0]                     pcie_vdm_sts4_dbg,
   output logic [63:0]                     pcie_vdm_sts5_dbg,
   
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
   input  logic                            avmm_ingr_mstr_waitreq,
   
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


localparam  MCTP_HDR_VERSION     = 4'h1;

logic [7:0]   cntr_1us;
logic         pulse_1us;

//-----------------------------------------------------------------------------
// Internal signal generation
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin
   if(reset) begin
      cntr_1us    <= 8'd0;
      pulse_1us   <= 1'b0;
   end else begin
      pulse_1us   <= (cntr_1us == 8'hFF) ? 1'b1 : 1'b0;
      cntr_1us    <= cntr_1us + 1'b1;
   end
end

//-----------------------------------------------------------------------------
// Ingress MCTP over PCIe VDM module
//-----------------------------------------------------------------------------
mctp_pcievdm_ingr #(
   .INGR_MSTR_ADDR_WIDTH   (INGR_MSTR_ADDR_WIDTH   ),
   .INGR_MSTR_BRST_WIDTH   (INGR_MSTR_BRST_WIDTH   ),
   .DEBUG_REG_EN           (DEBUG_REG_EN           ),
   .DEBUG_REG_WIDTH        (DEBUG_REG_WIDTH        ),
   .MCTP_HDR_VERSION       (MCTP_HDR_VERSION       ),
   .MCTP_BASELINE_MTU      (MCTP_BASELINE_MTU      )
)mctp_pcievdm_ingr_inst(
   .clk                    (clk                    ),
   .reset                  (reset                  ),
   
   //CSR i/f
   .pcievdm_mctp_eid       (pcievdm_mctp_eid       ),
// .pcievdm_mctp_mtu_wsize (),
   .pcievdm_afu_addr_vld   (pcievdm_afu_addr_vld   ),
   .pcie_vdm_sts1_dbg      (pcie_vdm_sts1_dbg      ),
   .pcie_vdm_sts2_dbg      (pcie_vdm_sts2_dbg      ),
   .pcie_vdm_sts3_dbg      (pcie_vdm_sts3_dbg      ),
   .pulse_1us              (pulse_1us              ),
   
   //Ingress AVMM slave (connected to IOFS-shell/AFU)
   .avmm_ingr_slv_addr     (avmm_ingr_slv_addr     ),
   .avmm_ingr_slv_write    (avmm_ingr_slv_write    ),
   .avmm_ingr_slv_read     (avmm_ingr_slv_read     ),
   .avmm_ingr_slv_wrdata   (avmm_ingr_slv_wrdata   ),
   .avmm_ingr_slv_byteen   (avmm_ingr_slv_byteen   ),
   .avmm_ingr_slv_rddata   (avmm_ingr_slv_rddata   ),
   .avmm_ingr_slv_rddvld   (avmm_ingr_slv_rddvld   ),
   .avmm_ingr_slv_waitreq  (avmm_ingr_slv_waitreq  ),

   //Ingress AVMM Master (connected to SPI Master)
   .avmm_ingr_mstr_addr    (avmm_ingr_mstr_addr    ),
   .avmm_ingr_mstr_write   (avmm_ingr_mstr_write   ),
   .avmm_ingr_mstr_read    (avmm_ingr_mstr_read    ),
   .avmm_ingr_mstr_burstcnt(avmm_ingr_mstr_burstcnt),
   .avmm_ingr_mstr_wrdata  (avmm_ingr_mstr_wrdata  ),
   .avmm_ingr_mstr_rddata  (avmm_ingr_mstr_rddata  ),
   .avmm_ingr_mstr_rddvld  (avmm_ingr_mstr_rddvld  ),
   .avmm_ingr_mstr_waitreq (avmm_ingr_mstr_waitreq )
);


//-----------------------------------------------------------------------------
// Egress MCTP over PCIe VDM module
//-----------------------------------------------------------------------------
mctp_pcievdm_egrs #(
   .EGRS_SLV_ADDR_WIDTH    (EGRS_SLV_ADDR_WIDTH   ),
   .SS_ADDR_WIDTH          (SS_ADDR_WIDTH         ),
   .DEBUG_REG_EN           (DEBUG_REG_EN          ),
   .DEBUG_REG_WIDTH        (DEBUG_REG_WIDTH       ),
   .MCTP_HDR_VERSION       (MCTP_HDR_VERSION      ),
   .MCTP_BASELINE_MTU      (MCTP_BASELINE_MTU     )
)mctp_pcievdm_egrs_inst(
   .clk                    (clk                   ),
   .reset                  (reset                 ),
   
   //CSR i/f
   .pcievdm_afu_addr       (pcievdm_afu_addr      ),
   .pcievdm_mctp_eid       (pcievdm_mctp_eid      ),
   .pcie_vdm_sts4_dbg      (pcie_vdm_sts4_dbg     ),
   .pcie_vdm_sts5_dbg      (pcie_vdm_sts5_dbg     ),
   .pulse_1us              (pulse_1us             ),
   
   //Egress AVMM slave (connected to SPI Slave)
   .avmm_egrs_slv_addr     (avmm_egrs_slv_addr    ),
   .avmm_egrs_slv_write    (avmm_egrs_slv_write   ),
   .avmm_egrs_slv_read     (avmm_egrs_slv_read    ),
   .avmm_egrs_slv_wrdata   (avmm_egrs_slv_wrdata  ),
   .avmm_egrs_slv_rddata   (avmm_egrs_slv_rddata  ),
   .avmm_egrs_slv_rddvld   (avmm_egrs_slv_rddvld  ),
   .avmm_egrs_slv_waitreq  (avmm_egrs_slv_waitreq ),

   //Egress AVMM Master (connected to IOFS-shell/AFU)
   .avmm_egrs_mstr_addr    (avmm_egrs_mstr_addr   ),
   .avmm_egrs_mstr_write   (avmm_egrs_mstr_write  ),
   .avmm_egrs_mstr_read    (avmm_egrs_mstr_read   ),
   .avmm_egrs_mstr_wrdata  (avmm_egrs_mstr_wrdata ),
   .avmm_egrs_mstr_byteen  (avmm_egrs_mstr_byteen ),
   .avmm_egrs_mstr_rddata  (avmm_egrs_mstr_rddata ),
   .avmm_egrs_mstr_rddvld  (avmm_egrs_mstr_rddvld ),
   .avmm_egrs_mstr_waitreq (avmm_egrs_mstr_waitreq)
);

endmodule 
