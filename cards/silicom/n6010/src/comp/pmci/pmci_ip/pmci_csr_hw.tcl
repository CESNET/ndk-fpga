# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

# 
# Description
# -----------------------------------------------------------------------------
# This is the _hw.tcl of PMCI CSR
# -----------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Module Properties
# -----------------------------------------------------------------------------
package require -exact qsys 20.3

set_module_property DESCRIPTION "PMCI Control and Status Registers"
set_module_property NAME pmci_csr
set_module_property VERSION 1.0
set_module_property GROUP "PMCI-SS Custom IP"
set_module_property DISPLAY_NAME "PMCI CSR"
set_module_property INSTANTIATE_IN_SYSTEM_MODULE true
set_module_property EDITABLE true
# set_module_property INTERNAL false
# set_module_property OPAQUE_ADDRESS_MAP true

set_module_property VALIDATION_CALLBACK     ip_validate
set_module_property ELABORATION_CALLBACK    ip_elaborate

# -----------------------------------------------------------------------------
# Files
# -----------------------------------------------------------------------------
add_fileset synth_fileset QUARTUS_SYNTH synth_callback_procedure
set_fileset_property synth_fileset TOP_LEVEL pmci_csr
# set_fileset_property synth_fileset ENABLE_RELATIVE_INCLUDE_PATHS false
# set_fileset_property synth_fileset ENABLE_FILE_OVERWRITE_MODE false
add_fileset simver_fileset SIM_VERILOG synth_callback_procedure
set_fileset_property simver_fileset TOP_LEVEL pmci_csr
add_fileset simvhd_fileset SIM_VHDL synth_callback_procedure
set_fileset_property simvhd_fileset TOP_LEVEL pmci_csr

# proc synth_callback_procedure { } {
proc synth_callback_procedure { entity_name } {
   add_fileset_file pmci_csr.sv SYSTEM_VERILOG PATH "./custom_ip/pmci_csr/pmci_csr.sv" TOP_LEVEL_FILE
}


# -----------------------------------------------------------------------------
# Parameters
# -----------------------------------------------------------------------------
add_parameter FLASH_ADDR_WIDTH INTEGER 28 "Address width of the flash"
set_parameter_property FLASH_ADDR_WIDTH DISPLAY_NAME "Flash Address Width"
set_parameter_property FLASH_ADDR_WIDTH GROUP "Flash Burst Master Properties"
set_parameter_property FLASH_ADDR_WIDTH UNITS None
set_parameter_property FLASH_ADDR_WIDTH HDL_PARAMETER true
set_parameter_property FLASH_ADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property FLASH_ADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property FLASH_ADDR_WIDTH ENABLED true
set_parameter_property FLASH_ADDR_WIDTH ALLOWED_RANGES { \
   "17:17 -   1Mb flash" \
   "18:18 -   2Mb flash" \
   "19:19 -   4Mb flash" \
   "20:20 -   8Mb flash" \
   "21:21 -  16Mb flash" \
   "22:22 -  32Mb flash" \
   "23:23 -  64Mb flash" \
   "24:24 - 128Mb flash" \
   "25:25 - 256Mb flash" \
   "26:26 - 512Mb flash" \
   "27:27 -   1Gb flash" \
   "28:28 -   2Gb flash" \
}

add_parameter FBM_FIFO_DEPTH INTEGER 9 "Depth of the Flash Burst Master's FIFO"
set_parameter_property FBM_FIFO_DEPTH DISPLAY_NAME "FBM FIFO Depth"
set_parameter_property FBM_FIFO_DEPTH GROUP "Flash Burst Master Properties"
set_parameter_property FBM_FIFO_DEPTH UNITS None
set_parameter_property FBM_FIFO_DEPTH HDL_PARAMETER true
set_parameter_property FBM_FIFO_DEPTH AFFECTS_ELABORATION true
set_parameter_property FBM_FIFO_DEPTH AFFECTS_GENERATION false
set_parameter_property FBM_FIFO_DEPTH ENABLED true
set_parameter_property FBM_FIFO_DEPTH ALLOWED_RANGES { \
   "6:6  -  32x64 FIFO" \
   "7:7  -  32x128 FIFO" \
   "8:8  -  32x256 FIFO" \
   "9:9  -  32x512 FIFO" \
   "10:10 -  32x1K FIFO" \
   "11:11 -  32x2K FIFO" \
   "12:12 -  32x4K FIFO" \
}

add_parameter SS_ADDR_WIDTH INTEGER 21 "Address width of IOFS sub systems. PMCI uses this as address width of its AXI master interface. This parameter restricts the IOFS address range PMCI can access."
set_parameter_property SS_ADDR_WIDTH DISPLAY_NAME "IOFS Access Address Width"
set_parameter_property SS_ADDR_WIDTH GROUP "IOFS Related Parameters"
set_parameter_property SS_ADDR_WIDTH UNITS None
set_parameter_property SS_ADDR_WIDTH HDL_PARAMETER true
set_parameter_property SS_ADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property SS_ADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property SS_ADDR_WIDTH ENABLED true
set_parameter_property SS_ADDR_WIDTH ALLOWED_RANGES {10:32}

add_parameter PCIE_SS_ADDR INTEGER 0x10000 "PCIe SS base address in BPF interconnect"
set_parameter_property PCIE_SS_ADDR DISPLAY_NAME "PCIe SS base address"
set_parameter_property PCIE_SS_ADDR GROUP "IOFS Related Parameters"
set_parameter_property PCIE_SS_ADDR UNITS None
set_parameter_property PCIE_SS_ADDR HDL_PARAMETER true
set_parameter_property PCIE_SS_ADDR AFFECTS_ELABORATION true
set_parameter_property PCIE_SS_ADDR AFFECTS_GENERATION false
set_parameter_property PCIE_SS_ADDR ENABLED true
set_parameter_property PCIE_SS_ADDR ALLOWED_RANGES {0x0:0x1FFFFF}
set_parameter_property PCIE_SS_ADDR DISPLAY_HINT hexadecimal

add_parameter HSSI_SS_ADDR INTEGER 0x60000 "HSSI SS base address in BPF interconnect"
set_parameter_property HSSI_SS_ADDR DISPLAY_NAME "HSSI SS base address"
set_parameter_property HSSI_SS_ADDR GROUP "IOFS Related Parameters"
set_parameter_property HSSI_SS_ADDR UNITS None
set_parameter_property HSSI_SS_ADDR HDL_PARAMETER true
set_parameter_property HSSI_SS_ADDR AFFECTS_ELABORATION true
set_parameter_property HSSI_SS_ADDR AFFECTS_GENERATION false
set_parameter_property HSSI_SS_ADDR ENABLED true
set_parameter_property HSSI_SS_ADDR ALLOWED_RANGES {0x0:0x1FFFFF}
set_parameter_property HSSI_SS_ADDR DISPLAY_HINT hexadecimal

add_parameter PCIEVDM_AFU_ADDR INTEGER 0x42000 "AFU's MCTP over PCIe VDM module's base address in BPF interconnect"
set_parameter_property PCIEVDM_AFU_ADDR DISPLAY_NAME "AFU's MCTP over PCIe VDM module's base address"
set_parameter_property PCIEVDM_AFU_ADDR GROUP "IOFS Related Parameters"
set_parameter_property PCIEVDM_AFU_ADDR UNITS None
set_parameter_property PCIEVDM_AFU_ADDR HDL_PARAMETER true
set_parameter_property PCIEVDM_AFU_ADDR AFFECTS_ELABORATION true
set_parameter_property PCIEVDM_AFU_ADDR AFFECTS_GENERATION false
set_parameter_property PCIEVDM_AFU_ADDR ENABLED true
set_parameter_property PCIEVDM_AFU_ADDR ALLOWED_RANGES {0x0:0x1FFFFF}
set_parameter_property PCIEVDM_AFU_ADDR DISPLAY_HINT hexadecimal

add_parameter QSFPA_CTRL_ADDR INTEGER 0x12000 "QSFP-A controller's base address in BPF interconnect"
set_parameter_property QSFPA_CTRL_ADDR DISPLAY_NAME "QSFP-A controller's base address"
set_parameter_property QSFPA_CTRL_ADDR GROUP "IOFS Related Parameters"
set_parameter_property QSFPA_CTRL_ADDR UNITS None
set_parameter_property QSFPA_CTRL_ADDR HDL_PARAMETER true
set_parameter_property QSFPA_CTRL_ADDR AFFECTS_ELABORATION true
set_parameter_property QSFPA_CTRL_ADDR AFFECTS_GENERATION false
set_parameter_property QSFPA_CTRL_ADDR ENABLED true
set_parameter_property QSFPA_CTRL_ADDR ALLOWED_RANGES {0x0:0x1FFFFF}
set_parameter_property QSFPA_CTRL_ADDR DISPLAY_HINT hexadecimal

add_parameter QSFPB_CTRL_ADDR INTEGER 0x13000 "QSFP-B controller's base address in BPF interconnect"
set_parameter_property QSFPB_CTRL_ADDR DISPLAY_NAME "QSFP-B controller's base address"
set_parameter_property QSFPB_CTRL_ADDR GROUP "IOFS Related Parameters"
set_parameter_property QSFPB_CTRL_ADDR UNITS None
set_parameter_property QSFPB_CTRL_ADDR HDL_PARAMETER true
set_parameter_property QSFPB_CTRL_ADDR AFFECTS_ELABORATION true
set_parameter_property QSFPB_CTRL_ADDR AFFECTS_GENERATION false
set_parameter_property QSFPB_CTRL_ADDR ENABLED true
set_parameter_property QSFPB_CTRL_ADDR ALLOWED_RANGES {0x0:0x1FFFFF}
set_parameter_property QSFPB_CTRL_ADDR DISPLAY_HINT hexadecimal

add_parameter QSPI_BAUDRATE INTEGER 2 "qSPI Flash Baudrate"
set_parameter_property QSPI_BAUDRATE DISPLAY_NAME "qSPI Flash Baudrate"
set_parameter_property QSPI_BAUDRATE GROUP "Flash Parameters"
set_parameter_property QSPI_BAUDRATE UNITS None
set_parameter_property QSPI_BAUDRATE HDL_PARAMETER true
set_parameter_property QSPI_BAUDRATE AFFECTS_ELABORATION true
set_parameter_property QSPI_BAUDRATE AFFECTS_GENERATION false
set_parameter_property QSPI_BAUDRATE ENABLED true
set_parameter_property QSPI_BAUDRATE ALLOWED_RANGES { \
   "2:Flash baudrate is 1/4 of PMCI core clock" \
   "3:Flash baudrate is 1/6 of PMCI core clock" \
   "4:Flash baudrate is 1/8 of PMCI core clock" \
}

add_parameter FLASH_MFC INTEGER 0 "qSPI Flash Manufacturer"
set_parameter_property FLASH_MFC DISPLAY_NAME "qSPI Flash Manufacturer"
set_parameter_property FLASH_MFC GROUP "Flash Parameters"
set_parameter_property FLASH_MFC UNITS None
set_parameter_property FLASH_MFC HDL_PARAMETER true
set_parameter_property FLASH_MFC AFFECTS_ELABORATION true
set_parameter_property FLASH_MFC AFFECTS_GENERATION false
set_parameter_property FLASH_MFC ENABLED true
set_parameter_property FLASH_MFC ALLOWED_RANGES { \
   "0:Micron Flash" \
   "1:Macronix Flash" \
}

add_parameter END_OF_LIST INTEGER 0 "PMCI's DFH End of List"
set_parameter_property END_OF_LIST DISPLAY_NAME "DFH End of List"
set_parameter_property END_OF_LIST GROUP "PMCI DFH Paramters"
set_parameter_property END_OF_LIST UNITS None
set_parameter_property END_OF_LIST HDL_PARAMETER true
set_parameter_property END_OF_LIST AFFECTS_ELABORATION true
set_parameter_property END_OF_LIST AFFECTS_GENERATION false
set_parameter_property END_OF_LIST ENABLED true
set_parameter_property END_OF_LIST ALLOWED_RANGES { \
   "0:0(PMCI is NOT the end of DFH list)" \
   "1:1(PMCI is the end of DFH list)" \
}

add_parameter NEXT_DFH_OFFSET INTEGER 0x20000 "Next DFH Offset"
set_parameter_property NEXT_DFH_OFFSET DISPLAY_NAME "Next DFH Offset"
set_parameter_property NEXT_DFH_OFFSET GROUP "PMCI DFH Paramters"
set_parameter_property NEXT_DFH_OFFSET UNITS None
set_parameter_property NEXT_DFH_OFFSET HDL_PARAMETER true
set_parameter_property NEXT_DFH_OFFSET AFFECTS_ELABORATION true
set_parameter_property NEXT_DFH_OFFSET AFFECTS_GENERATION false
set_parameter_property NEXT_DFH_OFFSET ENABLED true
set_parameter_property NEXT_DFH_OFFSET ALLOWED_RANGES {0x0:0xFFFFFF}
set_parameter_property NEXT_DFH_OFFSET DISPLAY_HINT hexadecimal

add_parameter FEAT_VER INTEGER 0x1 "PMCI's DFH Feature Revision"
set_parameter_property FEAT_VER DISPLAY_NAME "DFH Feature Revision"
set_parameter_property FEAT_VER GROUP "PMCI DFH Paramters"
set_parameter_property FEAT_VER UNITS None
set_parameter_property FEAT_VER HDL_PARAMETER true
set_parameter_property FEAT_VER AFFECTS_ELABORATION true
set_parameter_property FEAT_VER AFFECTS_GENERATION false
set_parameter_property FEAT_VER ENABLED true
set_parameter_property FEAT_VER ALLOWED_RANGES {0x0:0xF}

add_parameter FEAT_ID INTEGER 0x12 "PMCI's DFH Feature ID"
set_parameter_property FEAT_ID DISPLAY_NAME "DFH Feature ID"
set_parameter_property FEAT_ID GROUP "PMCI DFH Paramters"
set_parameter_property FEAT_ID UNITS None
set_parameter_property FEAT_ID HDL_PARAMETER true
set_parameter_property FEAT_ID AFFECTS_ELABORATION true
set_parameter_property FEAT_ID AFFECTS_GENERATION false
set_parameter_property FEAT_ID ENABLED true
set_parameter_property FEAT_ID ALLOWED_RANGES {0x0:0xFFF}
set_parameter_property FEAT_ID DISPLAY_HINT hexadecimal

# -----------------------------------------------------------------------------
# Port - Clock
# -----------------------------------------------------------------------------
add_interface clock clock end
set_interface_property clock ENABLED true
set_interface_property clock EXPORT_OF ""
set_interface_property clock PORT_NAME_MAP ""
set_interface_property clock CMSIS_SVD_VARIABLES ""
set_interface_property clock SVD_ADDRESS_GROUP ""
set_interface_property clock IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port clock clk clk Input 1

# -----------------------------------------------------------------------------
# Port - Reset
# -----------------------------------------------------------------------------
add_interface reset reset end
set_interface_property reset associatedClock clock
set_interface_property reset synchronousEdges DEASSERT
set_interface_property reset ENABLED true
set_interface_property reset EXPORT_OF ""
set_interface_property reset PORT_NAME_MAP ""
set_interface_property reset CMSIS_SVD_VARIABLES ""
set_interface_property reset SVD_ADDRESS_GROUP ""
set_interface_property reset IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port reset reset reset Input 1

# -----------------------------------------------------------------------------
# Port - Host AvMM Slave
# -----------------------------------------------------------------------------
add_interface host_avmm_slv avalon end
set_interface_property host_avmm_slv addressUnits WORDS
set_interface_property host_avmm_slv associatedClock clock
set_interface_property host_avmm_slv associatedReset reset
set_interface_property host_avmm_slv bitsPerSymbol 8
set_interface_property host_avmm_slv burstOnBurstBoundariesOnly false
set_interface_property host_avmm_slv burstcountUnits WORDS
set_interface_property host_avmm_slv explicitAddressSpan 0
set_interface_property host_avmm_slv holdTime 0
set_interface_property host_avmm_slv linewrapBursts false
set_interface_property host_avmm_slv maximumPendingReadTransactions 1
set_interface_property host_avmm_slv maximumPendingWriteTransactions 0
set_interface_property host_avmm_slv readLatency 0
set_interface_property host_avmm_slv readWaitTime 1
set_interface_property host_avmm_slv setupTime 0
set_interface_property host_avmm_slv timingUnits Cycles
set_interface_property host_avmm_slv writeWaitTime 0
set_interface_property host_avmm_slv ENABLED true
set_interface_property host_avmm_slv EXPORT_OF ""
set_interface_property host_avmm_slv PORT_NAME_MAP ""
set_interface_property host_avmm_slv CMSIS_SVD_VARIABLES ""
set_interface_property host_avmm_slv SVD_ADDRESS_GROUP ""

add_interface_port host_avmm_slv host_avmm_slv_write write Input 1
add_interface_port host_avmm_slv host_avmm_slv_read read Input 1
add_interface_port host_avmm_slv host_avmm_slv_addr address Input 5
add_interface_port host_avmm_slv host_avmm_slv_rddata readdata Output 64
add_interface_port host_avmm_slv host_avmm_slv_rddvld readdatavalid Output 1
add_interface_port host_avmm_slv host_avmm_slv_waitreq waitrequest Output 1
add_interface_port host_avmm_slv host_avmm_slv_wrdata writedata Input 64
add_interface_port host_avmm_slv host_avmm_slv_byteen byteenable Input 8

# -----------------------------------------------------------------------------
# Port - PMCI Nios AvMM Slave
# -----------------------------------------------------------------------------
add_interface pnios_avmm_slv avalon end
set_interface_property pnios_avmm_slv addressUnits WORDS
set_interface_property pnios_avmm_slv associatedClock clock
set_interface_property pnios_avmm_slv associatedReset reset
set_interface_property pnios_avmm_slv bitsPerSymbol 8
set_interface_property pnios_avmm_slv burstOnBurstBoundariesOnly false
set_interface_property pnios_avmm_slv burstcountUnits WORDS
set_interface_property pnios_avmm_slv explicitAddressSpan 0
set_interface_property pnios_avmm_slv holdTime 0
set_interface_property pnios_avmm_slv linewrapBursts false
set_interface_property pnios_avmm_slv maximumPendingReadTransactions 1
set_interface_property pnios_avmm_slv maximumPendingWriteTransactions 0
set_interface_property pnios_avmm_slv readLatency 0
set_interface_property pnios_avmm_slv readWaitTime 1
set_interface_property pnios_avmm_slv setupTime 0
set_interface_property pnios_avmm_slv timingUnits Cycles
set_interface_property pnios_avmm_slv writeWaitTime 0
set_interface_property pnios_avmm_slv ENABLED true
set_interface_property pnios_avmm_slv EXPORT_OF ""
set_interface_property pnios_avmm_slv PORT_NAME_MAP ""
set_interface_property pnios_avmm_slv CMSIS_SVD_VARIABLES ""
set_interface_property pnios_avmm_slv SVD_ADDRESS_GROUP ""

add_interface_port pnios_avmm_slv pnios_avmm_slv_write write Input 1
add_interface_port pnios_avmm_slv pnios_avmm_slv_read read Input 1
add_interface_port pnios_avmm_slv pnios_avmm_slv_addr address Input 3
add_interface_port pnios_avmm_slv pnios_avmm_slv_rddata readdata Output 32
add_interface_port pnios_avmm_slv pnios_avmm_slv_rddvld readdatavalid Output 1
add_interface_port pnios_avmm_slv pnios_avmm_slv_waitreq waitrequest Output 1
add_interface_port pnios_avmm_slv pnios_avmm_slv_wrdata writedata Input 32

# -----------------------------------------------------------------------------
# Port - MAX10 Nios AvMM Slave
# -----------------------------------------------------------------------------
add_interface mnios_avmm_slv avalon end
set_interface_property mnios_avmm_slv addressUnits WORDS
set_interface_property mnios_avmm_slv associatedClock clock
set_interface_property mnios_avmm_slv associatedReset reset
set_interface_property mnios_avmm_slv bitsPerSymbol 8
set_interface_property mnios_avmm_slv burstOnBurstBoundariesOnly false
set_interface_property mnios_avmm_slv burstcountUnits WORDS
set_interface_property mnios_avmm_slv explicitAddressSpan 0
set_interface_property mnios_avmm_slv holdTime 0
set_interface_property mnios_avmm_slv linewrapBursts false
set_interface_property mnios_avmm_slv maximumPendingReadTransactions 1
set_interface_property mnios_avmm_slv maximumPendingWriteTransactions 0
set_interface_property mnios_avmm_slv readLatency 0
set_interface_property mnios_avmm_slv readWaitTime 1
set_interface_property mnios_avmm_slv setupTime 0
set_interface_property mnios_avmm_slv timingUnits Cycles
set_interface_property mnios_avmm_slv writeWaitTime 0
set_interface_property mnios_avmm_slv ENABLED true
set_interface_property mnios_avmm_slv EXPORT_OF ""
set_interface_property mnios_avmm_slv PORT_NAME_MAP ""
set_interface_property mnios_avmm_slv CMSIS_SVD_VARIABLES ""
set_interface_property mnios_avmm_slv SVD_ADDRESS_GROUP ""

add_interface_port mnios_avmm_slv mnios_avmm_slv_write write Input 1
add_interface_port mnios_avmm_slv mnios_avmm_slv_read read Input 1
add_interface_port mnios_avmm_slv mnios_avmm_slv_addr address Input 2
add_interface_port mnios_avmm_slv mnios_avmm_slv_rddata readdata Output 32
add_interface_port mnios_avmm_slv mnios_avmm_slv_rddvld readdatavalid Output 1
add_interface_port mnios_avmm_slv mnios_avmm_slv_waitreq waitrequest Output 1
add_interface_port mnios_avmm_slv mnios_avmm_slv_wrdata writedata Input 32

# -----------------------------------------------------------------------------
# Port - Flash Burst Master interface (conduit)
# -----------------------------------------------------------------------------
add_interface fbm_if conduit end
set_interface_property fbm_if associatedClock clock
set_interface_property fbm_if associatedReset reset
set_interface_property fbm_if ENABLED true
set_interface_property fbm_if EXPORT_OF ""
set_interface_property fbm_if PORT_NAME_MAP ""
set_interface_property fbm_if CMSIS_SVD_VARIABLES ""
set_interface_property fbm_if SVD_ADDRESS_GROUP ""
set_interface_property fbm_if IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port fbm_if write_mode write_mode Output 1
add_interface_port fbm_if read_mode read_mode Output 1
add_interface_port fbm_if rsu_mode rsu_mode Output 1
add_interface_port fbm_if read_count read_count Output -1
add_interface_port fbm_if flash_busy flash_busy Input 1
add_interface_port fbm_if fifo_dcount fifo_dcount Input -1
add_interface_port fbm_if flash_addr flash_addr Output -1

# -----------------------------------------------------------------------------
# Port - MCTP over PCIe-VDM Controller interface (conduit)
# -----------------------------------------------------------------------------
add_interface mpc_if conduit end
set_interface_property mpc_if associatedClock clock
set_interface_property mpc_if associatedReset reset
set_interface_property mpc_if ENABLED true
set_interface_property mpc_if EXPORT_OF ""
set_interface_property mpc_if PORT_NAME_MAP ""
set_interface_property mpc_if CMSIS_SVD_VARIABLES ""
set_interface_property mpc_if SVD_ADDRESS_GROUP ""
set_interface_property mpc_if IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port mpc_if pcievdm_afu_addr pcievdm_afu_addr Output -1
add_interface_port mpc_if pcievdm_afu_addr_vld pcievdm_afu_addr_vld Output 1
add_interface_port mpc_if pcievdm_mctp_eid pcievdm_mctp_eid Output 8
add_interface_port mpc_if pcie_vdm_sts1_dbg pcie_vdm_sts1_dbg Input 64
add_interface_port mpc_if pcie_vdm_sts2_dbg pcie_vdm_sts2_dbg Input 64
add_interface_port mpc_if pcie_vdm_sts3_dbg pcie_vdm_sts3_dbg Input 64
add_interface_port mpc_if pcie_vdm_sts4_dbg pcie_vdm_sts4_dbg Input 64
add_interface_port mpc_if pcie_vdm_sts5_dbg pcie_vdm_sts5_dbg Input 64

# -----------------------------------------------------------------------------
# Port - PXEboot OptionROM Module interface (conduit)
# -----------------------------------------------------------------------------
add_interface orom_if conduit end
set_interface_property orom_if associatedClock clock
set_interface_property orom_if associatedReset reset
set_interface_property orom_if ENABLED true
set_interface_property orom_if EXPORT_OF ""
set_interface_property orom_if PORT_NAME_MAP ""
set_interface_property orom_if CMSIS_SVD_VARIABLES ""
set_interface_property orom_if SVD_ADDRESS_GROUP ""
set_interface_property orom_if IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port orom_if pxeboot_rd_start pxeboot_rd_start Output 1
add_interface_port orom_if pxeboot_status pxeboot_status Input 32

# -----------------------------------------------------------------------------
# Port - MAX10 interface (conduit)
# -----------------------------------------------------------------------------
add_interface m10_if conduit end
set_interface_property m10_if associatedClock clock
set_interface_property m10_if associatedReset reset
set_interface_property m10_if ENABLED true
set_interface_property m10_if EXPORT_OF ""
set_interface_property m10_if PORT_NAME_MAP ""
set_interface_property m10_if CMSIS_SVD_VARIABLES ""
set_interface_property m10_if SVD_ADDRESS_GROUP ""
set_interface_property m10_if IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port m10_if fpga_usr_100m fpga_usr_100m Input 1
add_interface_port m10_if fpga_m10_hb fpga_m10_hb Input 1
add_interface_port m10_if m10_seu_error m10_seu_error Input 1
add_interface_port m10_if fpga_therm_shdn fpga_therm_shdn Output 1
add_interface_port m10_if fpga_seu_error fpga_seu_error Output 1

# -----------------------------------------------------------------------------
# Port - SEU IP AvST Sink
# -----------------------------------------------------------------------------
add_interface seu_avst_sink avalon_streaming end                            
set_interface_property seu_avst_sink associatedClock clock                      
set_interface_property seu_avst_sink associatedReset reset                    
set_interface_property seu_avst_sink dataBitsPerSymbol 64                     
set_interface_property seu_avst_sink errorDescriptor ""                       
set_interface_property seu_avst_sink firstSymbolInHighOrderBits true          
set_interface_property seu_avst_sink maxChannel 0                             
set_interface_property seu_avst_sink readyAllowance 0                         
set_interface_property seu_avst_sink readyLatency 0                           
set_interface_property seu_avst_sink ENABLED true                             
set_interface_property seu_avst_sink EXPORT_OF ""                             
set_interface_property seu_avst_sink PORT_NAME_MAP ""                         
set_interface_property seu_avst_sink CMSIS_SVD_VARIABLES ""                   
set_interface_property seu_avst_sink SVD_ADDRESS_GROUP ""                     
set_interface_property seu_avst_sink IPXACT_REGISTER_MAP_VARIABLES ""         

add_interface_port seu_avst_sink seu_avst_sink_data data Input 64          
add_interface_port seu_avst_sink seu_avst_sink_vld valid Input 1         
add_interface_port seu_avst_sink seu_avst_sink_rdy ready Output 1   

# -----------------------------------------------------------------------------
# Port - SEU IP System Error (conduit)
# -----------------------------------------------------------------------------
add_interface seu_sys_err conduit end                                             
set_interface_property seu_sys_err associatedClock clock                            
set_interface_property seu_sys_err associatedReset reset                          
set_interface_property seu_sys_err ENABLED true                                   
set_interface_property seu_sys_err EXPORT_OF ""                                   
set_interface_property seu_sys_err PORT_NAME_MAP ""                               
set_interface_property seu_sys_err CMSIS_SVD_VARIABLES ""                         
set_interface_property seu_sys_err SVD_ADDRESS_GROUP ""                           
set_interface_property seu_sys_err IPXACT_REGISTER_MAP_VARIABLES ""               

add_interface_port seu_sys_err seu_sys_error sys_error Input 1

# -----------------------------------------------------------------------------
# Validate IP
# -----------------------------------------------------------------------------
proc ip_validate { } {
   

}

# -----------------------------------------------------------------------------
# Elaborate IP
# -----------------------------------------------------------------------------
proc ip_elaborate { } {
   
   set fadr_width [ get_parameter_value FLASH_ADDR_WIDTH ]
   set fbm_fdepth [ get_parameter_value FBM_FIFO_DEPTH ]
   set ssa_awidth [ get_parameter_value SS_ADDR_WIDTH ]
   
   set_port_property flash_addr width_expr $fadr_width
   set_port_property read_count width_expr [expr {$fbm_fdepth + 1}]
   set_port_property fifo_dcount width_expr [expr {$fbm_fdepth + 1}]
   set_port_property pcievdm_afu_addr width_expr $ssa_awidth
}
