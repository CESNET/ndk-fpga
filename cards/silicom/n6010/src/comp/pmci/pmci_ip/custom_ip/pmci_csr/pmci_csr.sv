// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
// This module implements the control and status registers of PMCI-SS.
//-----------------------------------------------------------------------------

module pmci_csr #(
   parameter   FLASH_ADDR_WIDTH   = 28,
   parameter   FBM_FIFO_DEPTH     = 9,
   parameter   SS_ADDR_WIDTH      = 21,
   parameter   PCIE_SS_ADDR       = 21'h10000,
   parameter   HSSI_SS_ADDR       = 21'h60000,
   parameter   PCIEVDM_AFU_ADDR   = 21'h42000,
   parameter   QSFPA_CTRL_ADDR    = 21'h12000,
   parameter   QSFPB_CTRL_ADDR    = 21'h13000,
   
   parameter   QSPI_BAUDRATE      = 5'd2,     //SPI Clock Baud-rate Register of flash controller
                                              //Valid values 0x2 -> /4, 0x3 -> /6 & 0x4 -> /8, 
   parameter   FLASH_MFC          = 1'b0,     //Flash device manufacturer 0 -> Micron, 1 -> Macronix
   
   parameter   END_OF_LIST        = 1'b0,     //DFH End of List
   parameter   NEXT_DFH_OFFSET    = 24'h20000,//Next DFH Offset
   parameter   FEAT_VER           = 4'h1,     //DFH Feature Revision
   parameter   FEAT_ID            = 12'h12    //DFH Feature ID
)(
   input  logic                        clk,
   input  logic                        reset,

   //Host AVMM slave
   input  logic [4:0]                  host_avmm_slv_addr,
   input  logic                        host_avmm_slv_write,
   input  logic                        host_avmm_slv_read,
   input  logic [63:0]                 host_avmm_slv_wrdata,
   input  logic [7:0]                  host_avmm_slv_byteen,
   output logic [63:0]                 host_avmm_slv_rddata,
   output logic                        host_avmm_slv_rddvld,
   output logic                        host_avmm_slv_waitreq,
 
   //PMCI Nios AVMM slave
   input  logic [2:0]                  pnios_avmm_slv_addr,
   input  logic                        pnios_avmm_slv_write,
   input  logic                        pnios_avmm_slv_read,
   input  logic [31:0]                 pnios_avmm_slv_wrdata,
   output logic [31:0]                 pnios_avmm_slv_rddata,
   output logic                        pnios_avmm_slv_rddvld,
   output logic                        pnios_avmm_slv_waitreq,
   
   //MAX10 Nios AVMM slave
   input  logic [1:0]                  mnios_avmm_slv_addr,
   input  logic                        mnios_avmm_slv_write,
   input  logic                        mnios_avmm_slv_read,
   input  logic [31:0]                 mnios_avmm_slv_wrdata,
   output logic [31:0]                 mnios_avmm_slv_rddata,
   output logic                        mnios_avmm_slv_rddvld,
   output logic                        mnios_avmm_slv_waitreq,
   
   //Flash burst master interface
   output logic                        write_mode,
   output logic                        read_mode,
   output logic                        rsu_mode,
   input  logic                        flash_busy ,
   input  logic [FBM_FIFO_DEPTH:0]     fifo_dcount,
   output logic [FBM_FIFO_DEPTH:0]     read_count,
   output logic [FLASH_ADDR_WIDTH-1:0] flash_addr,

   //MCTP over PCIeVDM Controller interface
   output logic [SS_ADDR_WIDTH-1:0]    pcievdm_afu_addr,
   output logic                        pcievdm_afu_addr_vld,
   output logic [7:0]                  pcievdm_mctp_eid,
   input  logic [63:0]                 pcie_vdm_sts1_dbg,
   input  logic [63:0]                 pcie_vdm_sts2_dbg,
   input  logic [63:0]                 pcie_vdm_sts3_dbg,
   input  logic [63:0]                 pcie_vdm_sts4_dbg,
   input  logic [63:0]                 pcie_vdm_sts5_dbg,
   
   //PXeboot OptionROM module interface
   output logic                        pxeboot_rd_start,
   input  logic [31:0]                 pxeboot_status,
   
   //SEU IP interface
   input  logic                        seu_sys_error,
   input  logic [63:0]                 seu_avst_sink_data,
   input  logic                        seu_avst_sink_vld,
   output logic                        seu_avst_sink_rdy,
   
   //MAX10-PMCI extra pins  (temporary assignment)
   input  logic                        fpga_usr_100m,
   input  logic                        fpga_m10_hb,
   output logic                        fpga_therm_shdn,
   output logic                        fpga_seu_error,
   input  logic                        m10_seu_error
);

localparam PMCI_DBG_MODE      = 0;
localparam PMCI_RTL_VERSION   = 16'h22;
localparam PMCI_DFH_FTYPE     = 4'h3;     //DFH Feature Type
localparam PMCI_DFH_RSVD      = 19'h0;    //DFH Reserved 

localparam TIME_CNTR_1_VAL    = 10'd998;  //10us counter
localparam TIME_CNTR_2_VAL    = 10'd399;  //4ms counter
localparam M10_NHB_TO_BIT     = 9; //512*4ms = 2.048sec timeout
localparam PMCI_NHB_TO_BIT    = 7; //128*4ms = 512msec timeout

//------------------------------------------------------------------------------
// Internal Declarations
//------------------------------------------------------------------------------
logic                         m10_seu_err_sync;
logic                         m10_nios_hb;
logic [SS_ADDR_WIDTH-1:0]     pcie_ss_addr;
logic [SS_ADDR_WIDTH-1:0]     hssi_ss_addr;
logic [SS_ADDR_WIDTH-1:0]     qsfpa_ctrl_addr;
logic [SS_ADDR_WIDTH-1:0]     qsfpb_ctrl_addr;
logic [63:0]                  pmci_dfh_reg;
logic [63:0]                  fbm_ctrl_sts_reg;
logic [63:0]                  pmci_error_reg;
logic [15:0]                  pmci_fw_version;
logic                         fpga_therm_shdn_i;
logic                         pmci_nios_hb;
logic                         pnios_flsh_cfg_done;
logic [31:0]                  pnios_misc_reg;
logic [9:0]                   time_cntr_1;
logic [9:0]                   time_cntr_2;
logic                         time_tick_1;
logic                         time_tick_2;
logic                         m10_nios_hb_r1;
logic                         pmci_nios_hb_r1;
logic [M10_NHB_TO_BIT:0]      m10_nhb_timer;
logic [PMCI_NHB_TO_BIT:0]     pmci_nhb_timer;
logic                         m10_nios_stuck;
logic                         pmci_nios_stuck;
logic                         flsh_wr_mode;
logic                         rst_time_cntr;
logic                         incr_time_cntr2;
logic [9:0]                   dbg_flsh_wr_tmr1;
logic [10:0]                  dbg_flsh_wr_tmr2;
logic                         dbg_flsh_wr_of;
logic [63:0]                  fbm_dbg_sts_reg;


//-----------------------------------------------------------------------------
// Synchronization
//-----------------------------------------------------------------------------
altera_std_synchronizer #(
   .depth   (2             )
) m10_seu_sync (
    .clk    (clk           ),
    .reset_n(~reset        ),
    .din    (m10_seu_error ),
    .dout   (m10_seu_err_sync )
);

altera_std_synchronizer #(
   .depth   (2             )
) m10_hb_sync (
    .clk    (clk           ),
    .reset_n(~reset        ),
    .din    (fpga_m10_hb   ),
    .dout   (m10_nios_hb   )
);

//-----------------------------------------------------------------------------
// IOFSHW subsystem base address
//-----------------------------------------------------------------------------
always_comb
begin : ss_baddr_comb
   pcievdm_afu_addr     = PCIEVDM_AFU_ADDR;
   pcievdm_afu_addr_vld = 1'b1; //if this is not OK then delay until DFH read detect
   
   pcie_ss_addr         = PCIE_SS_ADDR;
   hssi_ss_addr         = HSSI_SS_ADDR;
   qsfpa_ctrl_addr      = QSFPA_CTRL_ADDR;
   qsfpb_ctrl_addr      = QSFPB_CTRL_ADDR;
end : ss_baddr_comb

//-----------------------------------------------------------------------------
// IOFS-SW CSR write
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : host_csr_wr
   if(reset) begin
      write_mode           <= 1'b0;
      read_mode            <= 1'b0;
      read_count           <= {(FBM_FIFO_DEPTH+1){1'b0}};
      flash_addr           <= {FLASH_ADDR_WIDTH{1'b0}};
   end else if (host_avmm_slv_write && !host_avmm_slv_waitreq) begin
      if (host_avmm_slv_addr == 5'h8 && host_avmm_slv_byteen[3:0] == 4'hF) begin
         write_mode        <= (PMCI_DBG_MODE == 1) ? host_avmm_slv_wrdata[0] : 1'b0;
         read_mode         <= host_avmm_slv_wrdata[1];
         read_count        <= host_avmm_slv_wrdata[16+:10];
      end
      
      if (host_avmm_slv_addr == 5'h8 && host_avmm_slv_byteen[7:4] == 4'hF)
         flash_addr        <= host_avmm_slv_wrdata[32+:FLASH_ADDR_WIDTH];
   end
end : host_csr_wr

always_comb
begin : host_csr_comb
   pmci_dfh_reg[63:60] = PMCI_DFH_FTYPE;
   pmci_dfh_reg[59:41] = PMCI_DFH_RSVD;
   pmci_dfh_reg[40]    = END_OF_LIST;
   pmci_dfh_reg[39:16] = NEXT_DFH_OFFSET;
   pmci_dfh_reg[15:12] = FEAT_VER;
   pmci_dfh_reg[11:0]  = FEAT_ID;
   
   fbm_ctrl_sts_reg[0]      = write_mode;
   fbm_ctrl_sts_reg[1]      = read_mode;
   fbm_ctrl_sts_reg[2]      = flash_busy;
   fbm_ctrl_sts_reg[3]      = '0;
   fbm_ctrl_sts_reg[13:4]   = fifo_dcount;
   fbm_ctrl_sts_reg[15:14]  = '0;
   fbm_ctrl_sts_reg[25:16]  = read_count;
   fbm_ctrl_sts_reg[31:26]  = '0;
   fbm_ctrl_sts_reg[32+:FLASH_ADDR_WIDTH]    = flash_addr;
   fbm_ctrl_sts_reg[63:32+FLASH_ADDR_WIDTH]  = '0;
   
   pmci_error_reg[0]    = m10_seu_err_sync;
   pmci_error_reg[1]    = fpga_seu_error;
   pmci_error_reg[2]    = m10_nios_stuck;
   pmci_error_reg[3]    = pmci_nios_stuck;
   pmci_error_reg[4]    = seu_sys_error;
   pmci_error_reg[63:5] = '0;
   
end : host_csr_comb

//-----------------------------------------------------------------------------
// IOFS-SW CSR read
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : host_csr_rd_seq
   if(reset) begin
      host_avmm_slv_rddvld    <= 1'b0;
      host_avmm_slv_rddata    <= 64'd0;
   end else if (host_avmm_slv_read && !host_avmm_slv_waitreq) begin
      host_avmm_slv_rddvld    <= 1'b1;
      
      case (host_avmm_slv_addr)
         5'h0    : host_avmm_slv_rddata <= pmci_dfh_reg;
         
         5'h8    : host_avmm_slv_rddata <= fbm_ctrl_sts_reg;
         5'h9    : host_avmm_slv_rddata <= pmci_error_reg;
         5'hA    : host_avmm_slv_rddata <= {32'd0, pxeboot_status};
         5'h18   : host_avmm_slv_rddata <= pcie_vdm_sts1_dbg;
         5'h19   : host_avmm_slv_rddata <= pcie_vdm_sts2_dbg;
         5'h1A   : host_avmm_slv_rddata <= pcie_vdm_sts3_dbg;
         5'h1B   : host_avmm_slv_rddata <= pcie_vdm_sts4_dbg;
         5'h1C   : host_avmm_slv_rddata <= pcie_vdm_sts5_dbg;
         5'h1E   : host_avmm_slv_rddata <= fbm_dbg_sts_reg;
         5'h1F   : host_avmm_slv_rddata <= {32'd0, pmci_fw_version, PMCI_RTL_VERSION};
         default : host_avmm_slv_rddata <= 64'hBAADBEEF_DEADBEEF;
      endcase 
   end else begin
      host_avmm_slv_rddvld <= 1'b0;
   end
end : host_csr_rd_seq

assign host_avmm_slv_waitreq = 1'b0;

//-----------------------------------------------------------------------------
// PMCI Nios CSR write
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : pnios_csr_wr
   if(reset) begin
      pmci_fw_version     <= 16'hFFFF;
      fpga_therm_shdn_i   <= 1'b0;
      pmci_nios_hb        <= 1'b0;
      pnios_flsh_cfg_done <= 1'b0;
   end else if (pnios_avmm_slv_write && !pnios_avmm_slv_waitreq) begin
      if (pnios_avmm_slv_addr == 3'h0)
         pmci_fw_version   <= pnios_avmm_slv_wrdata[31:16];
      
      if (pnios_avmm_slv_addr == 3'h1)
         fpga_therm_shdn_i <= pnios_avmm_slv_wrdata[0];
      
      if (pnios_avmm_slv_addr == 3'h2)
         pmci_nios_hb      <= pnios_avmm_slv_wrdata[0];
      
      if (pnios_avmm_slv_addr == 3'h3)
         pnios_flsh_cfg_done  <= pnios_avmm_slv_wrdata[0];
   end
end : pnios_csr_wr

assign pnios_avmm_slv_waitreq = 1'b0;
assign fpga_therm_shdn        = fpga_therm_shdn_i ? 1'b0 : 1'bz;

//-----------------------------------------------------------------------------
// PMCI Nios CSR read
//-----------------------------------------------------------------------------
always_comb
begin : pnios_csr_comb
   pnios_misc_reg[0]     = pnios_flsh_cfg_done;
   pnios_misc_reg[15:1]  = '0;
   pnios_misc_reg[20:16] = QSPI_BAUDRATE;
   pnios_misc_reg[23:21] = '0;
   pnios_misc_reg[24]    = FLASH_MFC;
   pnios_misc_reg[31:25] = '0;
end : pnios_csr_comb

always_ff @(posedge clk, posedge reset)
begin : pnios_csr_rd
   if(reset) begin
      pnios_avmm_slv_rddvld  <= 1'b0;
      pnios_avmm_slv_rddata  <= 32'd0;
   end else if (pnios_avmm_slv_read && !pnios_avmm_slv_waitreq) begin
      pnios_avmm_slv_rddvld  <= 1'b1;
      case (pnios_avmm_slv_addr)
         3'h0    : pnios_avmm_slv_rddata <= {pmci_fw_version, PMCI_RTL_VERSION};
         3'h1    : pnios_avmm_slv_rddata <= {31'd0, fpga_therm_shdn_i};
         3'h2    : pnios_avmm_slv_rddata <= {31'd0, pmci_nios_hb};
         3'h3    : pnios_avmm_slv_rddata <= pnios_misc_reg;
         3'h4    : pnios_avmm_slv_rddata <= {{(32-SS_ADDR_WIDTH){1'b0}}, pcie_ss_addr};
         3'h5    : pnios_avmm_slv_rddata <= {{(32-SS_ADDR_WIDTH){1'b0}}, hssi_ss_addr};
         3'h6    : pnios_avmm_slv_rddata <= {{(32-SS_ADDR_WIDTH){1'b0}}, qsfpa_ctrl_addr};
         3'h7    : pnios_avmm_slv_rddata <= {{(32-SS_ADDR_WIDTH){1'b0}}, qsfpb_ctrl_addr};
         default : pnios_avmm_slv_rddata <= 32'hDEADBEEF;
      endcase
   end else begin
      pnios_avmm_slv_rddvld  <= 1'b0;
   end
end : pnios_csr_rd

//-----------------------------------------------------------------------------
// MAX10 Nios CSR write
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : mnios_csr_wr
   if(reset) begin
      rsu_mode          <= 1'b0;
      pcievdm_mctp_eid  <= 8'd0;
   end else begin
      if (mnios_avmm_slv_write && !mnios_avmm_slv_waitreq && mnios_avmm_slv_addr == 2'h1)
         rsu_mode  <= mnios_avmm_slv_wrdata[0];
      
      if (mnios_avmm_slv_write && !mnios_avmm_slv_waitreq && mnios_avmm_slv_addr == 2'h2)
         pcievdm_mctp_eid  <= mnios_avmm_slv_wrdata[7:0];
   end
end : mnios_csr_wr

assign mnios_avmm_slv_waitreq = 1'b0;


//-----------------------------------------------------------------------------
// MAX10 Nios CSR read
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : mnios_csr_rd
   if(reset) begin
      mnios_avmm_slv_rddvld  <= 1'b0;
      mnios_avmm_slv_rddata  <= 32'd0;
   end else if (mnios_avmm_slv_read && !mnios_avmm_slv_waitreq) begin
      mnios_avmm_slv_rddvld  <= 1'b1;
      case (mnios_avmm_slv_addr)
         2'h0    : mnios_avmm_slv_rddata <= {pmci_fw_version, PMCI_RTL_VERSION};
         2'h1    : mnios_avmm_slv_rddata <= {30'd0, flash_busy, rsu_mode};
         2'h2    : mnios_avmm_slv_rddata <= {24'd0, pcievdm_mctp_eid};
         default : mnios_avmm_slv_rddata <= 32'hDEADBEEF;
      endcase
   end else begin
      mnios_avmm_slv_rddvld  <= 1'b0;
   end
end : mnios_csr_rd

//-----------------------------------------------------------------------------
// FM61's SEU Detection
//-----------------------------------------------------------------------------
assign fpga_seu_error    = seu_avst_sink_vld;
assign seu_avst_sink_rdy = 1'b0;

//-----------------------------------------------------------------------------
// Time pulse generation
// time_tick_1 is a 10us tick
// time_tick_2 is a 4ms tick
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : time_pulse_seq
   if(reset) begin
      time_cntr_1    <= 10'd0;
      time_cntr_2    <= 10'd0;
      time_tick_1    <= 1'b0;
      time_tick_2    <= 1'b0;
   end else begin
      if(time_tick_1)
         time_cntr_1 <= 10'd0;
      else
         time_cntr_1 <= time_cntr_1 + 1'b1;
      
      time_tick_1    <= (time_cntr_1 == TIME_CNTR_1_VAL) ? 1'b1 : 1'b0;

      if(time_tick_2)
         time_cntr_2 <= 10'd0;
      else if(time_tick_1)
         time_cntr_2 <= time_cntr_2 + 1'b1;
      
      time_tick_2    <= (time_tick_1 && time_cntr_2 == TIME_CNTR_2_VAL) ? 1'b1 : 1'b0;
   end
end : time_pulse_seq

//-----------------------------------------------------------------------------
// Nios heartbeat monitor
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : nios_hb_mon
   if(reset) begin
      m10_nios_hb_r1  <= 1'b0;
      pmci_nios_hb_r1 <= 1'b0;
      m10_nhb_timer   <= {(M10_NHB_TO_BIT+1){1'b0}};
      pmci_nhb_timer  <= {(PMCI_NHB_TO_BIT+1){1'b0}};
   end else begin
      m10_nios_hb_r1  <= m10_nios_hb;
      pmci_nios_hb_r1 <= pmci_nios_hb;
      
      if(m10_nios_hb_r1 != m10_nios_hb)
         m10_nhb_timer <= {(M10_NHB_TO_BIT+1){1'b0}};
      else if(time_tick_2 && !m10_nios_stuck)
         m10_nhb_timer <= m10_nhb_timer + 1'b1;
      
      if(pmci_nios_hb_r1 != pmci_nios_hb)
         pmci_nhb_timer <= {(PMCI_NHB_TO_BIT+1){1'b0}};
      else if(time_tick_2 && !pmci_nios_stuck)
         pmci_nhb_timer <= pmci_nhb_timer + 1'b1;
   end
end : nios_hb_mon

assign m10_nios_stuck  = m10_nhb_timer[M10_NHB_TO_BIT];
assign pmci_nios_stuck = pmci_nhb_timer[PMCI_NHB_TO_BIT];


//-----------------------------------------------------------------------------
// PXEBoot Option ROM start reading flash indication.
// Start PXEboot Option ROM flash reading after flash controller is initialized 
// and after 10us after PMCI is out of reset.
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : orom_rd_start
   if(reset) begin
      pxeboot_rd_start  <= 1'b0;
   end else if(pnios_flsh_cfg_done && time_tick_1) begin
      pxeboot_rd_start  <= 1'b1;
   end
end : orom_rd_start

//-----------------------------------------------------------------------------
// Debug : RSU staging area write time measurement
//-----------------------------------------------------------------------------
always_ff @(posedge clk, posedge reset)
begin : dbg_flsh_wr_time
   if(reset) begin
      flsh_wr_mode     <= 1'b0;
      rst_time_cntr    <= 1'b0;
      incr_time_cntr2  <= 1'b0;
      dbg_flsh_wr_tmr1 <= 10'd0;
      dbg_flsh_wr_tmr2 <= 11'd0;
      dbg_flsh_wr_of   <= 1'b0;
   end else begin
      if (write_mode || rsu_mode)
         flsh_wr_mode   <= 1'b1;
      else if(!flash_busy)
         flsh_wr_mode   <= 1'b0;
         
      if ((write_mode || rsu_mode) && !flsh_wr_mode)
         rst_time_cntr   <= 1'b1;
      else
         rst_time_cntr   <= 1'b0;
         
      if (rst_time_cntr)
         dbg_flsh_wr_tmr1  <= 10'd0;
      else if(flsh_wr_mode && time_tick_2)
         dbg_flsh_wr_tmr1  <= dbg_flsh_wr_tmr1 + 1'b1;
      
      if(!rst_time_cntr && flsh_wr_mode && time_tick_2 && 
                                                   dbg_flsh_wr_tmr1 == 10'h3FF)
         incr_time_cntr2 <= 1'b1;
      else 
         incr_time_cntr2 <= 1'b0;

      if (rst_time_cntr)
         dbg_flsh_wr_tmr2  <= 11'd0;
      else if(incr_time_cntr2)
         dbg_flsh_wr_tmr2  <= dbg_flsh_wr_tmr2 + 1'b1;

      if (rst_time_cntr)
         dbg_flsh_wr_of  <= 1'b0;
      else if(dbg_flsh_wr_tmr2 == 11'h7FF && incr_time_cntr2)
         dbg_flsh_wr_of  <= 1'b1;
   end
end : dbg_flsh_wr_time

always_comb
begin
   fbm_dbg_sts_reg[1:0]   = '0;
   fbm_dbg_sts_reg[23:2]  = {dbg_flsh_wr_of, dbg_flsh_wr_tmr2, dbg_flsh_wr_tmr1};
   fbm_dbg_sts_reg[63:24] = '0;
end

endmodule 
