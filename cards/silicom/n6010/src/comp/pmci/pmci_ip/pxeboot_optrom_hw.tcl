# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

# 
# Description
# -----------------------------------------------------------------------------
# This is the _hw.tcl of PXEBoot OptionROM core
# -----------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Module Properties
# -----------------------------------------------------------------------------
package require -exact qsys 20.3

set_module_property DESCRIPTION "This module acts as a OptionROM of the PXEboot flow"
set_module_property NAME pxeboot_optrom
set_module_property VERSION 1.0
set_module_property GROUP "PMCI-SS Custom IP"
set_module_property DISPLAY_NAME "PXEBoot Option ROM"
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
set_fileset_property synth_fileset TOP_LEVEL pxeboot_optrom
# set_fileset_property synth_fileset ENABLE_RELATIVE_INCLUDE_PATHS false
# set_fileset_property synth_fileset ENABLE_FILE_OVERWRITE_MODE false
add_fileset simver_fileset SIM_VERILOG synth_callback_procedure
set_fileset_property simver_fileset TOP_LEVEL pxeboot_optrom
add_fileset simvhd_fileset SIM_VHDL synth_callback_procedure
set_fileset_property simvhd_fileset TOP_LEVEL pxeboot_optrom

# proc synth_callback_procedure { } {
proc synth_callback_procedure { entity_name } {
   add_fileset_file pxeboot_optrom.sv SYSTEM_VERILOG PATH "./custom_ip/pxeboot_optrom/pxeboot_optrom.sv" TOP_LEVEL_FILE
}


# -----------------------------------------------------------------------------
# Parameters
# -----------------------------------------------------------------------------
add_parameter OPTROM_AREA_BADDR INTEGER 0xB800000 "Base address of Option ROM in FPGA Flash"
set_parameter_property OPTROM_AREA_BADDR DISPLAY_NAME "Option ROM Flash Location Base Address"
set_parameter_property OPTROM_AREA_BADDR GROUP "Flash Properties"
set_parameter_property OPTROM_AREA_BADDR UNITS None
set_parameter_property OPTROM_AREA_BADDR HDL_PARAMETER true
set_parameter_property OPTROM_AREA_BADDR AFFECTS_ELABORATION true
set_parameter_property OPTROM_AREA_BADDR AFFECTS_GENERATION false
set_parameter_property OPTROM_AREA_BADDR ENABLED true
set_parameter_property OPTROM_AREA_BADDR DISPLAY_HINT hexadecimal

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

add_parameter HOST_RDADDR_WIDTH INTEGER 16 "Address width of host side AvMM read inteface"
set_parameter_property HOST_RDADDR_WIDTH DISPLAY_NAME "Host Side (Byte) Addres Width"
set_parameter_property HOST_RDADDR_WIDTH GROUP "Host I/f Properties"
set_parameter_property HOST_RDADDR_WIDTH UNITS None
set_parameter_property HOST_RDADDR_WIDTH HDL_PARAMETER true
set_parameter_property HOST_RDADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property HOST_RDADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property HOST_RDADDR_WIDTH ENABLED true
set_parameter_property HOST_RDADDR_WIDTH ALLOWED_RANGES { \
   "16:16  -  64KBytes Address Range for OptionROM" \
}

add_parameter OPTROM_SIZE INTEGER 32 "Option ROM size to be read from flash. Providing correct Option ROM size saves memory resources of FPGA."
set_parameter_property OPTROM_SIZE DISPLAY_NAME "Option ROM Size in KBytes"
set_parameter_property OPTROM_SIZE GROUP "Option ROM Properties"
set_parameter_property OPTROM_SIZE UNITS None
set_parameter_property OPTROM_SIZE HDL_PARAMETER true
set_parameter_property OPTROM_SIZE AFFECTS_ELABORATION true
set_parameter_property OPTROM_SIZE AFFECTS_GENERATION false
set_parameter_property OPTROM_SIZE ENABLED true
set_parameter_property OPTROM_SIZE ALLOWED_RANGES { \
   "16:16KBytes of OptionROM" \
   "32:32KBytes of OptionROM" \
   "64:64KBytes of OptionROM" \
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
add_interface_port avalon_master avmm_mstr_read read Output 1
add_interface_port avalon_master avmm_mstr_burstcnt burstcount Output 7
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

add_interface_port avalon_slave avmm_slv_read read Input 1
add_interface_port avalon_slave avmm_slv_addr address Input -1
add_interface_port avalon_slave avmm_slv_rddata readdata Output 64
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

add_interface_port csr_if pxeboot_rd_start pxeboot_rd_start Input 1
add_interface_port csr_if pxeboot_status pxeboot_status Output 32

# -----------------------------------------------------------------------------
# Validate IP
# -----------------------------------------------------------------------------
proc ip_validate { } {
   
   set orom_baddr [ get_parameter_value OPTROM_AREA_BADDR ]
   set fadr_width [ get_parameter_value FLASH_ADDR_WIDTH ]
   set hadr_width [ get_parameter_value HOST_RDADDR_WIDTH ]
   set orom_size  [ get_parameter_value OPTROM_SIZE ]

   set addr_span     [expr {pow(2, $fadr_width)}]
   
   if { $addr_span <= $orom_baddr } {
      send_message Error "Option ROM flash base addres is out of bound of flash address range. Please correct Option ROM base address or flash address width"
   }
   
   if { [expr {$orom_size * 1024}] > [expr {pow(2, $hadr_width)}] } {
      send_message Error "Option ROM size is out of bound of host address. Please correct Option ROM size or host address width"
   }
}

# -----------------------------------------------------------------------------
# Elaborate IP
# -----------------------------------------------------------------------------
proc ip_elaborate { } {
   
   set fadr_width [ get_parameter_value FLASH_ADDR_WIDTH ]
   set hadr_width [ get_parameter_value HOST_RDADDR_WIDTH ]

   set_port_property avmm_slv_addr  width_expr [expr {$hadr_width - 3}]
   set_port_property avmm_mstr_addr width_expr $fadr_width
}
