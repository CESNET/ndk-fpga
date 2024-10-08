# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

# 
# Description
# -----------------------------------------------------------------------------
# This is the _hw.tcl of Avalon Slave to SPI Master Bridge Core
# -----------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Module Properties
# -----------------------------------------------------------------------------
package require -exact qsys 20.3

set_module_property DESCRIPTION "This ia a SPI master bridge to access meomory mapped slave over Avalon-MM"
set_module_property NAME avmms_2_spim_bridge
set_module_property VERSION 1.0
set_module_property GROUP "PMCI-SS Custom IP"
set_module_property DISPLAY_NAME "Avalon Slave to SPI Master Bridge Core"
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
set_fileset_property synth_fileset TOP_LEVEL avmms_2_spim_bridge
# set_fileset_property synth_fileset ENABLE_RELATIVE_INCLUDE_PATHS false
# set_fileset_property synth_fileset ENABLE_FILE_OVERWRITE_MODE false
add_fileset simver_fileset SIM_VERILOG synth_callback_procedure
set_fileset_property simver_fileset TOP_LEVEL avmms_2_spim_bridge
add_fileset simvhd_fileset SIM_VHDL synth_callback_procedure
set_fileset_property simvhd_fileset TOP_LEVEL avmms_2_spim_bridge

# proc synth_callback_procedure { } {
proc synth_callback_procedure { entity_name } {
   add_fileset_file avmms_2_spim_bridge.sv SYSTEM_VERILOG PATH "./custom_ip/spi_master/avmms_2_spim_bridge.sv"
   add_fileset_file altera_avalon_st_bytes_to_packets.v VERILOG PATH "./custom_ip/spi_master/altera_avalon_st_bytes_to_packets.v"
   add_fileset_file altera_avalon_st_packets_to_bytes.v VERILOG PATH "./custom_ip/spi_master/altera_avalon_st_packets_to_bytes.v"
}

# -----------------------------------------------------------------------------
# Parameters
# -----------------------------------------------------------------------------
add_parameter CSR_DATA_WIDTH INTEGER 32 "AvMM data width of mailbox/CSR AvMM interface"
set_parameter_property CSR_DATA_WIDTH DISPLAY_NAME "CSR AvMM Interface Data Width"
set_parameter_property CSR_DATA_WIDTH GROUP "CSR AvMM Properties"
set_parameter_property CSR_DATA_WIDTH UNITS None
set_parameter_property CSR_DATA_WIDTH HDL_PARAMETER true
set_parameter_property CSR_DATA_WIDTH AFFECTS_ELABORATION true
set_parameter_property CSR_DATA_WIDTH AFFECTS_GENERATION false
set_parameter_property CSR_DATA_WIDTH ENABLED true
set_parameter_property CSR_DATA_WIDTH ALLOWED_RANGES { \
   "32:32 bits" \
   "64:64 bits" \
}

add_parameter CSR_ADDR_WIDTH INTEGER 3 "AvMM address width of mailbox/CSR AvMM interface"
set_parameter_property CSR_ADDR_WIDTH DISPLAY_NAME "CSR AvMM Interface Address Width"
set_parameter_property CSR_ADDR_WIDTH GROUP "CSR AvMM Properties"
set_parameter_property CSR_ADDR_WIDTH UNITS None
set_parameter_property CSR_ADDR_WIDTH HDL_PARAMETER true
set_parameter_property CSR_ADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property CSR_ADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property CSR_ADDR_WIDTH ENABLED true
set_parameter_property CSR_ADDR_WIDTH DERIVED true
set_parameter_property CSR_ADDR_WIDTH ALLOWED_RANGES { \
   "2:2 - for 64bit data interface" \
   "3:3 - for 32bit data interface" \
}

add_parameter SLV_CSR_AWIDTH INTEGER 16 "Address width of Slave address for CSR based SPI slave access. This paramter is derived from 'Base Address of Direct Slave Access'"
set_parameter_property SLV_CSR_AWIDTH DISPLAY_NAME "CSR Slave Address Width"
set_parameter_property SLV_CSR_AWIDTH GROUP "CSR AvMM Properties"
set_parameter_property SLV_CSR_AWIDTH UNITS None
set_parameter_property SLV_CSR_AWIDTH HDL_PARAMETER true
set_parameter_property SLV_CSR_AWIDTH AFFECTS_ELABORATION true
set_parameter_property SLV_CSR_AWIDTH AFFECTS_GENERATION false
set_parameter_property SLV_CSR_AWIDTH ENABLED true
set_parameter_property SLV_CSR_AWIDTH DERIVED true
set_parameter_property SLV_CSR_AWIDTH ALLOWED_RANGES {1:32}

add_parameter DIR_ADDR_WIDTH INTEGER 9 "AvMM word address width of direct slave access AvMM interface"
set_parameter_property DIR_ADDR_WIDTH DISPLAY_NAME "Direct AvMM Interface Word Address Width"
set_parameter_property DIR_ADDR_WIDTH GROUP "Direct AvMM Properties"
set_parameter_property DIR_ADDR_WIDTH UNITS None
set_parameter_property DIR_ADDR_WIDTH HDL_PARAMETER true
set_parameter_property DIR_ADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property DIR_ADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property DIR_ADDR_WIDTH ENABLED true
set_parameter_property DIR_ADDR_WIDTH ALLOWED_RANGES { \
   "1:1   -    8 Bytes" \
   "2:2   -   16 Bytes" \
   "3:3   -   32 Bytes" \
   "4:4   -   64 Bytes" \
   "5:5   -  128 Bytes" \
   "6:6   -  256 Bytes" \
   "7:7   -  512 Bytes" \
   "8:8   -   1K Bytes" \
   "9:9   -   2K Bytes" \
   "10:10 -   4K Bytes" \
   "11:11 -   8K Bytes" \
   "12:12 -  16K Bytes" \
   "13:13 -  32K Bytes" \
   "14:14 -  64K Bytes" \
   "15:15 - 128K Bytes" \
   "16:16 - 256K Bytes" \
   "17:17 - 512K Bytes" \
   "18:18 -   1M Bytes" \
   "19:19 -   2M Bytes" \
   "20:20 -   4M Bytes" \
   "21:21 -   8M Bytes" \
   "22:22 -  16M Bytes" \
   "23:23 -  32M Bytes" \
   "24:24 -  64M Bytes" \
   "25:25 - 128M Bytes" \
   "26:26 - 256M Bytes" \
   "27:27 - 512M Bytes" \
   "28:28 -   1G Bytes" \
   "29:29 -   2G Bytes" \
   "30:30 -   4G Bytes" \
}

add_parameter DIR_BASE_ADDR INTEGER 0x00010000 "Base address of the slave's CSR for direct SPI slave access. This paramter derives 'CSR Slave Address Width' paramter."
set_parameter_property DIR_BASE_ADDR DISPLAY_NAME "Base Address of Direct Slave Access"
set_parameter_property DIR_BASE_ADDR GROUP "Direct AvMM Properties"
set_parameter_property DIR_BASE_ADDR UNITS None
set_parameter_property DIR_BASE_ADDR HDL_PARAMETER true
set_parameter_property DIR_BASE_ADDR AFFECTS_ELABORATION true
set_parameter_property DIR_BASE_ADDR AFFECTS_GENERATION false
set_parameter_property DIR_BASE_ADDR ENABLED true
set_parameter_property DIR_BASE_ADDR DISPLAY_HINT hexadecimal

add_parameter DIR_BRST_WIDTH INTEGER 9 "AvMM burstcount width of direct slave access AvMM interface"
set_parameter_property DIR_BRST_WIDTH DISPLAY_NAME "Direct AvMM Interface Burstcount Width"
set_parameter_property DIR_BRST_WIDTH GROUP "Direct AvMM Properties"
set_parameter_property DIR_BRST_WIDTH UNITS None
set_parameter_property DIR_BRST_WIDTH HDL_PARAMETER true
set_parameter_property DIR_BRST_WIDTH AFFECTS_ELABORATION true
set_parameter_property DIR_BRST_WIDTH AFFECTS_GENERATION false
set_parameter_property DIR_BRST_WIDTH ENABLED true
set_parameter_property DIR_BRST_WIDTH ALLOWED_RANGES { \
   "1:1   -  Maximum 4 Bytes" \
   "2:2   -  Maximum 8 Bytes" \
   "3:3   -  Maximum 16 Bytes" \
   "4:4   -  Maximum 32 Bytes" \
   "5:5   -  Maximum 64 Bytes" \
   "6:6   -  Maximum 128 Bytes" \
   "7:7   -  Maximum 256 Bytes" \
   "8:8   -  Maximum 512 Bytes" \
   "9:9   -  Maximum 1K Bytes" \
   "10:10 -  Maximum 2K Bytes" \
   "11:11 -  Maximum 4K Bytes" \
   "12:12 -  Maximum 8K Bytes" \
   "13:13 -  Maximum 16K Bytes" \
   "14:14 -  Maximum 32K Bytes" \
}

add_parameter SCLK_CLK_DIV INTEGER 0 "Clock divider for SPI clock generation"
set_parameter_property SCLK_CLK_DIV DISPLAY_NAME "SPI Clock Divider"
set_parameter_property SCLK_CLK_DIV GROUP "SPI I/f Properties"
set_parameter_property SCLK_CLK_DIV UNITS None
set_parameter_property SCLK_CLK_DIV HDL_PARAMETER true
set_parameter_property SCLK_CLK_DIV AFFECTS_ELABORATION false
set_parameter_property SCLK_CLK_DIV ENABLED true
set_parameter_property SCLK_CLK_DIV ALLOWED_RANGES { \
   "0:0   - Ref clock / 2" \
   "1:1   - Ref clock / 4" \
   "2:2   - Ref clock / 6" \
   "3:3   - Ref clock / 8" \
   "4:4   - Ref clock / 10" \
   "5:5   - Ref clock / 12" \
   "6:6   - Ref clock / 14" \
   "7:7   - Ref clock / 16" \
   "8:8   - Ref clock / 18" \
   "9:9   - Ref clock / 20" \
   "10:10 - Ref clock / 22" \
   "11:11 - Ref clock / 24" \
   "12:12 - Ref clock / 26" \
   "13:13 - Ref clock / 28" \
   "14:14 - Ref clock / 30" \
   "15:15 - Ref clock / 32" \
}

add_parameter MISO_CAPT_DLY INTEGER 1 "SPI MISO capture delay in terms of reference clock cycles. Value 0 means no delay."
set_parameter_property MISO_CAPT_DLY DISPLAY_NAME "SPI MISO Capture Delay"
set_parameter_property MISO_CAPT_DLY GROUP "SPI I/f Properties"
set_parameter_property MISO_CAPT_DLY UNITS None
set_parameter_property MISO_CAPT_DLY HDL_PARAMETER true
set_parameter_property MISO_CAPT_DLY AFFECTS_ELABORATION false
set_parameter_property MISO_CAPT_DLY ENABLED true
set_parameter_property MISO_CAPT_DLY ALLOWED_RANGES {0:16}

add_parameter SPI_DEBUG_EN INTEGER 1 "Enable debug registers for the SPI master bridge"
set_parameter_property SPI_DEBUG_EN DISPLAY_NAME "SPI Debug Enable"
set_parameter_property SPI_DEBUG_EN GROUP "Misc."
set_parameter_property SPI_DEBUG_EN UNITS None
set_parameter_property SPI_DEBUG_EN HDL_PARAMETER true
set_parameter_property SPI_DEBUG_EN AFFECTS_ELABORATION false
set_parameter_property SPI_DEBUG_EN ENABLED true
set_parameter_property SPI_DEBUG_EN ALLOWED_RANGES { \
   "0:Disable debug registers" \
   "1:Enable debug registers" \
}

add_parameter USE_MEMORY_BLOCKS INTEGER 1 "Use memory block for FIFO or not"
set_parameter_property USE_MEMORY_BLOCKS DISPLAY_NAME "Use memory block for FIFO?"
set_parameter_property USE_MEMORY_BLOCKS GROUP "Misc."
set_parameter_property USE_MEMORY_BLOCKS UNITS None
set_parameter_property USE_MEMORY_BLOCKS HDL_PARAMETER true
set_parameter_property USE_MEMORY_BLOCKS AFFECTS_ELABORATION false
set_parameter_property USE_MEMORY_BLOCKS ENABLED true
set_parameter_property USE_MEMORY_BLOCKS ALLOWED_RANGES { \
   "0:Don't use memory block, use MLABs instead" \
   "1:Use memory blocks" \
}

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
# Port - CSR AvMM
# -----------------------------------------------------------------------------
add_interface avmm_csr avalon end
set_interface_property avmm_csr addressUnits WORDS
set_interface_property avmm_csr associatedClock clock
set_interface_property avmm_csr associatedReset reset
set_interface_property avmm_csr bitsPerSymbol 8
set_interface_property avmm_csr burstOnBurstBoundariesOnly false
set_interface_property avmm_csr burstcountUnits WORDS
set_interface_property avmm_csr explicitAddressSpan 0
set_interface_property avmm_csr holdTime 0
set_interface_property avmm_csr linewrapBursts false
set_interface_property avmm_csr maximumPendingReadTransactions 1
set_interface_property avmm_csr maximumPendingWriteTransactions 0
set_interface_property avmm_csr readLatency 0
set_interface_property avmm_csr readWaitTime 1
set_interface_property avmm_csr setupTime 0
set_interface_property avmm_csr timingUnits Cycles
set_interface_property avmm_csr writeWaitTime 0
set_interface_property avmm_csr ENABLED true
set_interface_property avmm_csr EXPORT_OF ""
set_interface_property avmm_csr PORT_NAME_MAP ""
set_interface_property avmm_csr CMSIS_SVD_VARIABLES ""
set_interface_property avmm_csr SVD_ADDRESS_GROUP ""

add_interface_port avmm_csr avmm_csr_write write Input 1
add_interface_port avmm_csr avmm_csr_read read Input 1
add_interface_port avmm_csr avmm_csr_addr address Input -1
add_interface_port avmm_csr avmm_csr_rddata readdata Output -1
add_interface_port avmm_csr avmm_csr_rddvld readdatavalid Output 1
add_interface_port avmm_csr avmm_csr_waitreq waitrequest Output 1
add_interface_port avmm_csr avmm_csr_wrdata writedata Input -1
add_interface_port avmm_csr avmm_csr_byteen byteenable Input -1
# set_interface_assignment avmm_csr embeddedsw.configuration.isFlash 0
# set_interface_assignment avmm_csr embeddedsw.configuration.isMemoryDevice 0
# set_interface_assignment avmm_csr embeddedsw.configuration.isNonVolatileStorage 0
# set_interface_assignment avmm_csr embeddedsw.configuration.isPrintableDevice 0

# -----------------------------------------------------------------------------
# Port - Direct AvMM
# -----------------------------------------------------------------------------
add_interface avmm_dir avalon end
set_interface_property avmm_dir addressUnits WORDS
set_interface_property avmm_dir associatedClock clock
set_interface_property avmm_dir associatedReset reset
set_interface_property avmm_dir bitsPerSymbol 8
set_interface_property avmm_dir burstOnBurstBoundariesOnly false
set_interface_property avmm_dir burstcountUnits WORDS
set_interface_property avmm_dir explicitAddressSpan 0
set_interface_property avmm_dir holdTime 0
set_interface_property avmm_dir linewrapBursts false
set_interface_property avmm_dir maximumPendingReadTransactions 1
set_interface_property avmm_dir maximumPendingWriteTransactions 0
set_interface_property avmm_dir readLatency 0
set_interface_property avmm_dir readWaitTime 1
set_interface_property avmm_dir setupTime 0
set_interface_property avmm_dir timingUnits Cycles
set_interface_property avmm_dir writeWaitTime 0
set_interface_property avmm_dir ENABLED true
set_interface_property avmm_dir EXPORT_OF ""
set_interface_property avmm_dir PORT_NAME_MAP ""
set_interface_property avmm_dir CMSIS_SVD_VARIABLES ""
set_interface_property avmm_dir SVD_ADDRESS_GROUP ""

add_interface_port avmm_dir avmm_dir_write write Input 1
add_interface_port avmm_dir avmm_dir_read read Input 1
add_interface_port avmm_dir avmm_dir_addr address Input -1
add_interface_port avmm_dir avmm_dir_burstcnt burstcount Input -1
add_interface_port avmm_dir avmm_dir_rddata readdata Output 32
add_interface_port avmm_dir avmm_dir_rddvld readdatavalid Output 1
add_interface_port avmm_dir avmm_dir_waitreq waitrequest Output 1
add_interface_port avmm_dir avmm_dir_wrdata writedata Input 32
# set_interface_assignment avmm_dir embeddedsw.configuration.isFlash 0
# set_interface_assignment avmm_dir embeddedsw.configuration.isMemoryDevice 0
# set_interface_assignment avmm_dir embeddedsw.configuration.isNonVolatileStorage 0
# set_interface_assignment avmm_dir embeddedsw.configuration.isPrintableDevice 0

# -----------------------------------------------------------------------------
# Port - SPI (conduit)
# -----------------------------------------------------------------------------
add_interface spi conduit end
set_interface_property spi associatedClock clock
set_interface_property spi associatedReset reset
set_interface_property spi ENABLED true
set_interface_property spi EXPORT_OF ""
set_interface_property spi PORT_NAME_MAP ""
set_interface_property spi CMSIS_SVD_VARIABLES ""
set_interface_property spi SVD_ADDRESS_GROUP ""

add_interface_port spi spim_clk sclk Output 1
add_interface_port spi spim_csn csn Output 1
add_interface_port spi spim_miso miso Input 1
add_interface_port spi spim_mosi mosi Output 1

# -----------------------------------------------------------------------------
# Validate IP
# -----------------------------------------------------------------------------
proc ip_validate { } {
   
   set csr_dwidth [ get_parameter_value CSR_DATA_WIDTH ]
   set dir_awidth [ get_parameter_value DIR_ADDR_WIDTH ]
   set dir_baddr  [ get_parameter_value DIR_BASE_ADDR ]
   set dir_bcount [ get_parameter_value DIR_BRST_WIDTH ]
   set clk_div    [ get_parameter_value SCLK_CLK_DIV ]
   set miso_dly   [ get_parameter_value MISO_CAPT_DLY ]

   #set_parameter_value CSR_ADDR_WIDTH [expr { int(log([expr {256 / $csr_dwidth}]) / log(2)) }]
   if { $csr_dwidth == 64 } {
      set_parameter_value CSR_ADDR_WIDTH 2
   } elseif { $csr_dwidth == 32 } {
      set_parameter_value CSR_ADDR_WIDTH 3
   } else {
      set_parameter_value CSR_ADDR_WIDTH -1
   }
   
   set addr_span  [expr {int(4 * pow(2, $dir_awidth))}]
   set max_bcount [expr {int(2 * pow(2, $dir_bcount))}]
   
   if { $max_bcount > $addr_span } {
      send_message Error "Addressable bytes derived from DIR_ADDR_WIDTH is lesser than maximum burst length derived from DIR_BRST_WIDTH"
      send_message Info "Address width spans $addr_span bytes."
      send_message Info "Maximum burst count is $max_bcount bytes."
   }
   
   if { $dir_baddr == 0 } {
      send_message Error "'Base Address of Direct Slave Access' cannot be zero"
   }
   if { $dir_baddr < 256 } {
      send_message Warning "'Base Address of Direct Slave Access' is too small value"
   }
   send_message Info "'Base Address of Direct Slave Access' should be more than CSR slave access address range"
   if { [expr {$dir_baddr & ($addr_span - 1)}] != 0 } {
      send_message Error [format "Base address 0x%X is not aligned to address range $addr_span bytes" $dir_baddr]
   }
   
   set bit_pos 31
   set all_fs 0xFFFFFFFF
   while { ([expr {$dir_baddr & ($all_fs << $bit_pos)}] != $dir_baddr) && ($bit_pos >= 0) } {
      set bit_pos [expr {$bit_pos - 1}]
   }
   set_parameter_value SLV_CSR_AWIDTH $bit_pos
   
   if { $miso_dly > [expr {$clk_div + 1}] } {
      send_message Warning "MISO Capture delay is more than clock period. Please make sure master can capture MISO at this delay"
   }
    
}

# -----------------------------------------------------------------------------
# Elaborate IP
# -----------------------------------------------------------------------------
proc ip_elaborate { } {
   
   set csr_awidth [ get_parameter_value CSR_ADDR_WIDTH ]
   set csr_dwidth [ get_parameter_value CSR_DATA_WIDTH ]
   set dir_awidth [ get_parameter_value DIR_ADDR_WIDTH ]
   set dir_bcount [ get_parameter_value DIR_BRST_WIDTH ]
   
   set_port_property avmm_csr_addr width_expr $csr_awidth
   set_port_property avmm_csr_rddata width_expr $csr_dwidth
   set_port_property avmm_csr_wrdata width_expr $csr_dwidth
   set_port_property avmm_csr_byteen width_expr [expr {$csr_dwidth / 8}]
   
   set_port_property avmm_dir_addr width_expr $dir_awidth
   set_port_property avmm_dir_burstcnt width_expr $dir_bcount

# sc_fifo
   add_hdl_instance             spi_sc_fifo altera_avalon_sc_fifo 19.3.2
   set_instance_parameter_value spi_sc_fifo {BITS_PER_SYMBOL} {32}
   set_instance_parameter_value spi_sc_fifo {CHANNEL_WIDTH} {0}
   set_instance_parameter_value spi_sc_fifo {EMPTY_LATENCY} {3}
   set_instance_parameter_value spi_sc_fifo {ENABLE_EXPLICIT_MAXCHANNEL} {0}
   set_instance_parameter_value spi_sc_fifo {ERROR_WIDTH} {0}
   set_instance_parameter_value spi_sc_fifo {EXPLICIT_MAXCHANNEL} {0}
   set_instance_parameter_value spi_sc_fifo {FIFO_DEPTH} {16}
   set_instance_parameter_value spi_sc_fifo {SYMBOLS_PER_BEAT} {1}
   set_instance_parameter_value spi_sc_fifo {SYNC_RESET} {0}
   set_instance_parameter_value spi_sc_fifo {USE_ALMOST_EMPTY_IF} {0}
   set_instance_parameter_value spi_sc_fifo {USE_ALMOST_FULL_IF} {0}
   set_instance_parameter_value spi_sc_fifo {USE_FILL_LEVEL} {0}
   set_instance_parameter_value spi_sc_fifo {USE_MEMORY_BLOCKS} {1}
   set_instance_parameter_value spi_sc_fifo {USE_PACKETS} {1}
   set_instance_parameter_value spi_sc_fifo {USE_STORE_FORWARD} {0}



}
