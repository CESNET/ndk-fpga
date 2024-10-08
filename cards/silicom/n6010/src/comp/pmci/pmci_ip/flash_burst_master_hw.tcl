# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

# 
# Description
# -----------------------------------------------------------------------------
# This is the _hw.tcl of Flash Burst Master core
# -----------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Module Properties
# -----------------------------------------------------------------------------
package require -exact qsys 20.3

set_module_property DESCRIPTION "This ia a AvMM burst transaction generator by aggregating non-burst transactions to improve flash performance"
set_module_property NAME flash_burst_master
set_module_property VERSION 1.0
set_module_property GROUP "PMCI-SS Custom IP"
set_module_property DISPLAY_NAME "Flash Burst Master"
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
set_fileset_property synth_fileset TOP_LEVEL flash_burst_master
# set_fileset_property synth_fileset ENABLE_RELATIVE_INCLUDE_PATHS false
# set_fileset_property synth_fileset ENABLE_FILE_OVERWRITE_MODE false
add_fileset simver_fileset SIM_VERILOG synth_callback_procedure
set_fileset_property simver_fileset TOP_LEVEL flash_burst_master
add_fileset simvhd_fileset SIM_VHDL synth_callback_procedure
set_fileset_property simvhd_fileset TOP_LEVEL flash_burst_master

# proc synth_callback_procedure { } {
proc synth_callback_procedure { entity_name } {
   add_fileset_file flash_burst_master.sv SYSTEM_VERILOG PATH "./custom_ip/flash_burst_master/flash_burst_master.sv" TOP_LEVEL_FILE
#  add_fileset_file scfifo.sv SYSTEM_VERILOG PATH "scfifo.sv"
}


# -----------------------------------------------------------------------------
# Parameters
# -----------------------------------------------------------------------------
add_parameter FLASH_ADDR_WIDTH INTEGER 28 "Address width of the flash"
set_parameter_property FLASH_ADDR_WIDTH DISPLAY_NAME "Flash Address Width"
set_parameter_property FLASH_ADDR_WIDTH GROUP "Flash Properties"
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

add_parameter STAGING_AREA_BADDR INTEGER 0xC800000 "Base address of staging area in FPGA Flash"
set_parameter_property STAGING_AREA_BADDR DISPLAY_NAME "Staging Area Base Address"
set_parameter_property STAGING_AREA_BADDR GROUP "Flash Properties"
set_parameter_property STAGING_AREA_BADDR UNITS None
set_parameter_property STAGING_AREA_BADDR HDL_PARAMETER true
set_parameter_property STAGING_AREA_BADDR AFFECTS_ELABORATION true
set_parameter_property STAGING_AREA_BADDR AFFECTS_GENERATION false
set_parameter_property STAGING_AREA_BADDR ENABLED true
set_parameter_property STAGING_AREA_BADDR DISPLAY_HINT hexadecimal

add_parameter FIFO_DEPTH_LOG2 INTEGER 9 "Depth of the FIFO used to aggregate write requests and store read data"
set_parameter_property FIFO_DEPTH_LOG2 DISPLAY_NAME "FIFO Depth"
set_parameter_property FIFO_DEPTH_LOG2 GROUP "FIFO Properties"
set_parameter_property FIFO_DEPTH_LOG2 UNITS None
set_parameter_property FIFO_DEPTH_LOG2 HDL_PARAMETER true
set_parameter_property FIFO_DEPTH_LOG2 AFFECTS_ELABORATION true
set_parameter_property FIFO_DEPTH_LOG2 AFFECTS_GENERATION false
set_parameter_property FIFO_DEPTH_LOG2 ENABLED true
set_parameter_property FIFO_DEPTH_LOG2 ALLOWED_RANGES { \
   "6:6  -  32x64 FIFO" \
   "7:7  -  32x128 FIFO" \
   "8:8  -  32x256 FIFO" \
   "9:9  -  32x512 FIFO" \
   "10:10 -  32x1K FIFO" \
   "11:11 -  32x2K FIFO" \
   "12:12 -  32x4K FIFO" \
}

add_parameter USE_MEMORY_BLOCKS INTEGER 1 "Use memory block for FIFO or not"
set_parameter_property USE_MEMORY_BLOCKS DISPLAY_NAME "Use memory block for FIFO?"
set_parameter_property USE_MEMORY_BLOCKS GROUP "FIFO Properties"
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
# Port - Avalon-MM master (to flash controller)
# -----------------------------------------------------------------------------
add_interface avalon_master avalon start
set_interface_property avalon_master addressGroup 0
set_interface_property avalon_master addressUnits SYMBOLS
set_interface_property avalon_master associatedClock clock
set_interface_property avalon_master associatedReset reset
set_interface_property avalon_master bitsPerSymbol 8
set_interface_property avalon_master burstOnBurstBoundariesOnly false
set_interface_property avalon_master burstcountUnits WORDS
set_interface_property avalon_master doStreamReads false
set_interface_property avalon_master doStreamWrites false
set_interface_property avalon_master holdTime 0
set_interface_property avalon_master linewrapBursts false
set_interface_property avalon_master maximumPendingReadTransactions 0
set_interface_property avalon_master maximumPendingWriteTransactions 0
set_interface_property avalon_master minimumResponseLatency 1
set_interface_property avalon_master readLatency 0
set_interface_property avalon_master readWaitTime 1
set_interface_property avalon_master setupTime 0
set_interface_property avalon_master timingUnits Cycles
set_interface_property avalon_master waitrequestAllowance 0
set_interface_property avalon_master writeWaitTime 0
set_interface_property avalon_master ENABLED true
set_interface_property avalon_master EXPORT_OF ""
set_interface_property avalon_master PORT_NAME_MAP ""
set_interface_property avalon_master CMSIS_SVD_VARIABLES ""
set_interface_property avalon_master SVD_ADDRESS_GROUP ""
set_interface_property avalon_master IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port avalon_master avmm_mstr_addr address Output -1
add_interface_port avalon_master avmm_mstr_write write Output 1
add_interface_port avalon_master avmm_mstr_read read Output 1
add_interface_port avalon_master avmm_mstr_burstcnt burstcount Output 7
add_interface_port avalon_master avmm_mstr_wrdata writedata Output 32
add_interface_port avalon_master avmm_mstr_rddata readdata Input 32
add_interface_port avalon_master avmm_mstr_rddvld readdatavalid Input 1
add_interface_port avalon_master avmm_mstr_waitreq waitrequest Input 1


# -----------------------------------------------------------------------------
# Port - Avalon-MM slave (to IOFS-shell/host)
# ----------------------------------------------------------------------------- 
add_interface avalon_slave avalon end
set_interface_property avalon_slave addressGroup 0
set_interface_property avalon_slave addressUnits WORDS
set_interface_property avalon_slave associatedClock clock
set_interface_property avalon_slave associatedReset reset
set_interface_property avalon_slave bitsPerSymbol 8
set_interface_property avalon_slave bridgedAddressOffset ""
set_interface_property avalon_slave bridgesToMaster avalon_master
set_interface_property avalon_slave burstOnBurstBoundariesOnly false
set_interface_property avalon_slave burstcountUnits WORDS
set_interface_property avalon_slave explicitAddressSpan 0
set_interface_property avalon_slave holdTime 0
set_interface_property avalon_slave linewrapBursts false
set_interface_property avalon_slave maximumPendingReadTransactions 1
set_interface_property avalon_slave maximumPendingWriteTransactions 0
set_interface_property avalon_slave minimumResponseLatency 1
set_interface_property avalon_slave readLatency 0
set_interface_property avalon_slave readWaitTime 1
set_interface_property avalon_slave setupTime 0
set_interface_property avalon_slave timingUnits Cycles
set_interface_property avalon_slave transparentBridge false
set_interface_property avalon_slave waitrequestAllowance 0
set_interface_property avalon_slave writeWaitTime 0
set_interface_property avalon_slave ENABLED true
set_interface_property avalon_slave EXPORT_OF ""
set_interface_property avalon_slave PORT_NAME_MAP ""
set_interface_property avalon_slave CMSIS_SVD_VARIABLES ""
set_interface_property avalon_slave SVD_ADDRESS_GROUP ""
set_interface_property avalon_slave IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port avalon_slave avmm_slv_write write Input 1
add_interface_port avalon_slave avmm_slv_read read Input 1
add_interface_port avalon_slave avmm_slv_addr address Input 8
add_interface_port avalon_slave avmm_slv_wrdata writedata Input 32
add_interface_port avalon_slave avmm_slv_byteen byteenable Input 4
add_interface_port avalon_slave avmm_slv_rddata readdata Output 32
add_interface_port avalon_slave avmm_slv_rddvld readdatavalid Output 1
add_interface_port avalon_slave avmm_slv_waitreq waitrequest Output 1
# set_interface_assignment avalon_slave embeddedsw.configuration.isFlash 0
# set_interface_assignment avalon_slave embeddedsw.configuration.isMemoryDevice 0
# set_interface_assignment avalon_slave embeddedsw.configuration.isNonVolatileStorage 0
# set_interface_assignment avalon_slave embeddedsw.configuration.isPrintableDevice 0


# -----------------------------------------------------------------------------
# Port - CSR interface (conduit)
# -----------------------------------------------------------------------------
add_interface csr_if conduit end
set_interface_property csr_if associatedClock clock
set_interface_property csr_if associatedReset reset
set_interface_property csr_if ENABLED true
set_interface_property csr_if EXPORT_OF ""
set_interface_property csr_if PORT_NAME_MAP ""
set_interface_property csr_if CMSIS_SVD_VARIABLES ""
set_interface_property csr_if SVD_ADDRESS_GROUP ""
set_interface_property csr_if IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port csr_if write_mode write_mode Input 1
add_interface_port csr_if read_mode read_mode Input 1
add_interface_port csr_if rsu_mode rsu_mode Input 1
add_interface_port csr_if read_count read_count Input -1
add_interface_port csr_if flash_busy flash_busy Output 1
add_interface_port csr_if fifo_dcount fifo_dcount Output -1
add_interface_port csr_if flash_addr flash_addr Input -1

# -----------------------------------------------------------------------------
# Validate IP
# -----------------------------------------------------------------------------
proc ip_validate { } {
   
   set sa_baddr [ get_parameter_value STAGING_AREA_BADDR ]
   set fadr_width [ get_parameter_value FLASH_ADDR_WIDTH ]
   set fifo_depth [ get_parameter_value FIFO_DEPTH_LOG2 ]

   set addr_span     [expr {pow(2, $fadr_width)}]
   
   if { $addr_span <= $sa_baddr } {
      send_message Error "Staging area base addres is out of bound of flash address range"
   } elseif {$sa_baddr < [expr {($addr_span * 3) / 4}]} {
      send_message Warning [format "Make sure staging area base address 0x%X is correct" $sa_baddr]
   }
}

# -----------------------------------------------------------------------------
# Elaborate IP
# -----------------------------------------------------------------------------
proc ip_elaborate { } {
   
   set sa_baddr [ get_parameter_value STAGING_AREA_BADDR ]
   set fadr_width [ get_parameter_value FLASH_ADDR_WIDTH ]
   set fifo_depth [ get_parameter_value FIFO_DEPTH_LOG2 ]

   set_port_property read_count     width_expr [expr {$fifo_depth + 1}]
   set_port_property fifo_dcount    width_expr [expr {$fifo_depth + 1}]
   set_port_property flash_addr     width_expr $fadr_width
   set_port_property avmm_mstr_addr width_expr $fadr_width
}
