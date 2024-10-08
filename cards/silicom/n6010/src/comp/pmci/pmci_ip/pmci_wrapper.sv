 
// Copyright (C) 2020 Intel Corporation.
// SPDX-License-Identifier: MIT

//
// Description
//-----------------------------------------------------------------------------
//
// Top level module of PMCI subsystem.
//
//-----------------------------------------------------------------------------

`include "fpga_defines.vh"

module pmci_wrapper  # (
   parameter bit [11:0] FEAT_ID         = 12'h012,
   parameter bit [3:0]  FEAT_VER        = 4'h1,
   parameter bit [23:0] NEXT_DFH_OFFSET = 24'h1000,
   parameter bit        END_OF_LIST     = 1'b0,
   parameter pmci_csr_PCIE_SS_ADDR      = 65536,
   parameter pmci_csr_HSSI_SS_ADDR      = 393216,
   parameter pmci_csr_PCIEVDM_AFU_ADDR  = 270336,
   parameter pmci_csr_QSFPA_CTRL_ADDR   = 73728,
   parameter pmci_csr_QSFPB_CTRL_ADDR   = 77824,
   parameter pmci_csr_END_OF_LIST       = 0,
   parameter pmci_csr_NEXT_DFH_OFFSET   = 131072,
   parameter pmci_csr_FEAT_VER          = 1,
   parameter pmci_csr_FEAT_ID           = 18

)(
  // AXI clock and reset
  input  wire        clk_csr,                                              
  input  wire        reset_csr,                                            
  ofs_fim_axi_lite_if.slave   csr_lite_slv_if,
  ofs_fim_axi_lite_if.master  csr_lite_mst_if,

  // AC FPGA - AC card BMC interface 
  output wire        qspi_dclk,               
  output wire        qspi_ncs,                
  inout  wire [3:0]  qspi_data,               
  input  wire        ncsi_rbt_ncsi_clk,       
  input  wire [1:0]  ncsi_rbt_ncsi_txd,       
  input  wire        ncsi_rbt_ncsi_tx_en,     
  output wire [1:0]  ncsi_rbt_ncsi_rxd,       
  output wire        ncsi_rbt_ncsi_crs_dv,    
  input  wire        ncsi_rbt_ncsi_arb_in,    
  output wire        ncsi_rbt_ncsi_arb_out,   
  input  wire        m10_gpio_fpga_usr_100m,  
  input  wire        m10_gpio_fpga_m10_hb,    
  input  wire        m10_gpio_m10_seu_error,  
  output wire        m10_gpio_fpga_therm_shdn,
  output wire        m10_gpio_fpga_seu_error, 
  output wire        spi_ingress_sclk,        
  output wire        spi_ingress_csn,         
  input  wire        spi_ingress_miso,        
  output wire        spi_ingress_mosi,        
  input  wire        spi_egress_mosi,         
  input  wire        spi_egress_csn,          
  input  wire        spi_egress_sclk,         
  output wire        spi_egress_miso          
 );
	  
wire  [2:0] slv_awsize;
wire  [2:0] slv_arsize;
logic [7:0] axi_mstr_awid_sig;
logic [7:0] axi_mstr_bid_sig;
logic [7:0] axi_mstr_arid_sig;
logic [7:0] axi_mstr_rid_sig;

assign slv_awsize   = ( &csr_lite_slv_if.wstrb )        ?   3'b011 :    // 8-byte
                                                            3'b010;     // 4-byte

assign slv_arsize   = ( csr_lite_slv_if.araddr[2] )     ?   3'b010 :    // 4-byte
                                                            3'b011;     // 8-byte

// AXI master AWID and ARID are latched and mapped as a response to the BID and RID respectively.
// This arrangement will work as long as there is request vs response pair maintained.
// This will not work when requests are send one after other from master before receiving the response
always_ff @(posedge clk_csr) begin
  if (reset_csr) 
  begin
    axi_mstr_bid_sig <= 8'b0;
	axi_mstr_rid_sig <= 8'b0;
  end
  if (csr_lite_mst_if.awvalid && csr_lite_mst_if.awready) 
  begin
    axi_mstr_bid_sig <= axi_mstr_awid_sig;
  end 
  if (csr_lite_mst_if.arvalid && csr_lite_mst_if.arready)
  begin
    axi_mstr_rid_sig <= axi_mstr_arid_sig;
  end
end

  pmci_ss #( .pmci_csr_PCIE_SS_ADDR    (pmci_csr_PCIE_SS_ADDR    ), 
	     .pmci_csr_HSSI_SS_ADDR    (pmci_csr_HSSI_SS_ADDR    ), 
	     .pmci_csr_PCIEVDM_AFU_ADDR(pmci_csr_PCIEVDM_AFU_ADDR), 
	     .pmci_csr_QSFPA_CTRL_ADDR (pmci_csr_QSFPA_CTRL_ADDR ), 
	     .pmci_csr_QSFPB_CTRL_ADDR (pmci_csr_QSFPB_CTRL_ADDR ), 
	     .pmci_csr_END_OF_LIST     (pmci_csr_END_OF_LIST     ), 
	     .pmci_csr_NEXT_DFH_OFFSET (pmci_csr_NEXT_DFH_OFFSET ), 
	     .pmci_csr_FEAT_VER        (pmci_csr_FEAT_VER        ), 
	     .pmci_csr_FEAT_ID         (pmci_csr_FEAT_ID         ),
             .pmci_csr_QSPI_BAUDRATE   (5'd2),                                       
             .pmci_csr_FLASH_MFC       (1'b0)             
   ) pmci_ss (
      .axi_mstr_awid                                              (axi_mstr_awid_sig             ),                                 
      .axi_mstr_awaddr                                            (csr_lite_mst_if.awaddr        ),           
      .axi_mstr_awprot                                            (csr_lite_mst_if.awprot[2:0]   ),      
      .axi_mstr_awvalid                                           (csr_lite_mst_if.awvalid       ),          
      .axi_mstr_awready                                           (csr_lite_mst_if.awready       ),          
      .axi_mstr_wdata                                             (csr_lite_mst_if.wdata         ),            
      .axi_mstr_wstrb                                             (csr_lite_mst_if.wstrb         ),            
      .axi_mstr_wlast                                             (                              ),                                 
      .axi_mstr_wvalid                                            (csr_lite_mst_if.wvalid        ),           
      .axi_mstr_wready                                            (csr_lite_mst_if.wready        ),           
      .axi_mstr_bid                                               (axi_mstr_bid_sig              ),                                
      .axi_mstr_bresp                                             (csr_lite_mst_if.bresp         ),            
      .axi_mstr_bvalid                                            (csr_lite_mst_if.bvalid        ),           
      .axi_mstr_bready                                            (csr_lite_mst_if.bready        ),           
      .axi_mstr_arid                                              (axi_mstr_arid_sig             ),                                 
      .axi_mstr_araddr                                            (csr_lite_mst_if.araddr        ),           
      .axi_mstr_arprot                                            (csr_lite_mst_if.arprot        ),           
      .axi_mstr_arvalid                                           (csr_lite_mst_if.arvalid       ),          
      .axi_mstr_arready                                           (csr_lite_mst_if.arready       ),          
      .axi_mstr_rid                                               (axi_mstr_rid_sig              ),                                
      .axi_mstr_rdata                                             (csr_lite_mst_if.rdata         ),            
      .axi_mstr_rresp                                             (csr_lite_mst_if.rresp         ),            
      .axi_mstr_rvalid                                            (csr_lite_mst_if.rvalid        ),           
      .axi_mstr_rready                                            (csr_lite_mst_if.rready        ),           
      .axi_slave_awid                                             (8'b0                          ),                                
      .axi_slave_awaddr                                           (csr_lite_slv_if.awaddr        ),           
      .axi_slave_awlen                                            (8'b0                          ),                                
      .axi_slave_awsize                                           (slv_awsize                    ),                       
      .axi_slave_awburst                                          (2'b0                          ),                                
      .axi_slave_awprot                                           (csr_lite_slv_if.awprot        ),       
      .axi_slave_awvalid                                          (csr_lite_slv_if.awvalid       ),      
      .axi_slave_awready                                          (csr_lite_slv_if.awready       ),      
      .axi_slave_wdata                                            (csr_lite_slv_if.wdata         ),        
      .axi_slave_wstrb                                            (csr_lite_slv_if.wstrb         ),        
      .axi_slave_wvalid                                           (csr_lite_slv_if.wvalid        ),       
      .axi_slave_wready                                           (csr_lite_slv_if.wready        ),       
      .axi_slave_bid                                              (                              ),                             
      .axi_slave_bresp                                            (csr_lite_slv_if.bresp         ),        
      .axi_slave_bvalid                                           (csr_lite_slv_if.bvalid        ),       
      .axi_slave_bready                                           (csr_lite_slv_if.bready        ),       
      .axi_slave_arid                                             (8'b0                          ),                            
      .axi_slave_araddr                                           (csr_lite_slv_if.araddr        ),       
      .axi_slave_arlen                                            (8'b0                          ),                            
      .axi_slave_arsize                                           (slv_arsize                    ),                   
      .axi_slave_arburst                                          (2'b0                          ),                            
      .axi_slave_arprot                                           (csr_lite_slv_if.arprot        ),       
      .axi_slave_arvalid                                          (csr_lite_slv_if.arvalid       ),      
      .axi_slave_arready                                          (csr_lite_slv_if.arready       ),      
      .axi_slave_rid                                              (                              ),                             
      .axi_slave_rdata                                            (csr_lite_slv_if.rdata         ),        
      .axi_slave_rresp                                            (csr_lite_slv_if.rresp         ),        
      .axi_slave_rlast                                            (                              ),                             
      .axi_slave_rvalid                                           (csr_lite_slv_if.rvalid        ),       
      .axi_slave_rready                                           (csr_lite_slv_if.rready        ),       
      .clk_clk                                                    (clk_csr                       ),                               
	  .qspi_dclk                                                  (qspi_dclk                     ),                                                   
	  .qspi_ncs                                                   (qspi_ncs                      ),                                                    
	  .qspi_data                                                  (qspi_data                     ),                                                   
      .ncsi_rbt_ncsi_clk                                          (ncsi_rbt_ncsi_clk             ),                               
      .ncsi_rbt_ncsi_txd                                          (ncsi_rbt_ncsi_txd             ),                               
      .ncsi_rbt_ncsi_tx_en                                        (ncsi_rbt_ncsi_tx_en           ),                               
      .ncsi_rbt_ncsi_rxd                                          (ncsi_rbt_ncsi_rxd             ),                               
      .ncsi_rbt_ncsi_crs_dv                                       (ncsi_rbt_ncsi_crs_dv          ),                               
      .ncsi_rbt_ncsi_arb_in                                       (ncsi_rbt_ncsi_arb_in          ),                               
      .ncsi_rbt_ncsi_arb_out                                      (ncsi_rbt_ncsi_arb_out         ),                               
      .m10_gpio_fpga_usr_100m                                     (m10_gpio_fpga_usr_100m        ),                               
      .m10_gpio_fpga_m10_hb                                       (m10_gpio_fpga_m10_hb          ),                               
      .m10_gpio_m10_seu_error                                     (m10_gpio_m10_seu_error        ),                               
      .m10_gpio_fpga_therm_shdn                                   (m10_gpio_fpga_therm_shdn      ),                               
      .m10_gpio_fpga_seu_error                                    (m10_gpio_fpga_seu_error       ),                               
      .reset_reset                                                (reset_csr                     ),                               
      .spi_ingress_sclk                                           (spi_ingress_sclk              ),                               
      .spi_ingress_csn                                            (spi_ingress_csn               ),                               
      .spi_ingress_miso                                           (spi_ingress_miso              ),                               
      .spi_ingress_mosi                                           (spi_ingress_mosi              ),                               
      .spi_egress_mosi_to_the_spislave_inst_for_spichain          (spi_egress_mosi               ),
      .spi_egress_nss_to_the_spislave_inst_for_spichain           (spi_egress_csn                ),
      .spi_egress_sclk_to_the_spislave_inst_for_spichain          (spi_egress_sclk               ),        
      .spi_egress_miso_to_and_from_the_spislave_inst_for_spichain (spi_egress_miso               ) 
	  
	);
 
endmodule
