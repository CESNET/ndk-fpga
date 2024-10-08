# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

# 
# Description
# -----------------------------------------------------------------------------
# This is the _hw.tcl of MCTP over PCIeVDM Controller
# -----------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Module Properties
# -----------------------------------------------------------------------------
package require -exact qsys 20.3

set_module_property DESCRIPTION "This is MCTP over PCIeVDM TLP endpoint with MCTP payload to/from MAX10 transfer logic"
set_module_property NAME mctp_pcievdm_ctrlr
set_module_property VERSION 1.0
set_module_property GROUP "PMCI-SS Custom IP"
set_module_property DISPLAY_NAME "MCTP over PCIeVDM Controller"
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
set_fileset_property synth_fileset TOP_LEVEL mctp_pcievdm_ctrlr
# set_fileset_property synth_fileset ENABLE_RELATIVE_INCLUDE_PATHS false
# set_fileset_property synth_fileset ENABLE_FILE_OVERWRITE_MODE false
add_fileset simver_fileset SIM_VERILOG synth_callback_procedure
set_fileset_property simver_fileset TOP_LEVEL mctp_pcievdm_ctrlr
add_fileset simvhd_fileset SIM_VHDL synth_callback_procedure
set_fileset_property simvhd_fileset TOP_LEVEL mctp_pcievdm_ctrlr

# proc synth_callback_procedure { } {
proc synth_callback_procedure { entity_name } {
   add_fileset_file mctp_pcievdm_ctrlr.sv SYSTEM_VERILOG PATH "./custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_ctrlr.sv" TOP_LEVEL_FILE
   add_fileset_file mctp_pcievdm_ingr.sv SYSTEM_VERILOG PATH "./custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_ingr.sv"
   add_fileset_file mctp_pcievdm_egrs.sv SYSTEM_VERILOG PATH "./custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_egrs.sv"
}


# -----------------------------------------------------------------------------
# Parameters
# -----------------------------------------------------------------------------
add_parameter INGR_MSTR_ADDR_WIDTH INTEGER 12 "Address width of the ingress master AvMM interface"
set_parameter_property INGR_MSTR_ADDR_WIDTH DISPLAY_NAME "Ingress Master AvMM Address Width"
# set_parameter_property INGR_MSTR_ADDR_WIDTH GROUP ""
set_parameter_property INGR_MSTR_ADDR_WIDTH UNITS None
set_parameter_property INGR_MSTR_ADDR_WIDTH HDL_PARAMETER true
set_parameter_property INGR_MSTR_ADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property INGR_MSTR_ADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property INGR_MSTR_ADDR_WIDTH ENABLED true
set_parameter_property INGR_MSTR_ADDR_WIDTH ALLOWED_RANGES { \
   "9:9  - 512 Bytes" \
   "10:10 - 1K Bytes" \
   "11:11 - 2K Bytes" \
   "12:12 - 4K Bytes" \
   "13:13 - 8K Bytes" \
   "14:14 - 16K Bytes" \
}

add_parameter INGR_MSTR_BRST_WIDTH INTEGER 9 "AvMM burstcount width of ingress master AvMM interface"
set_parameter_property INGR_MSTR_BRST_WIDTH DISPLAY_NAME "Ingress Master AvMM Burstcount Width"
# set_parameter_property INGR_MSTR_BRST_WIDTH GROUP ""
set_parameter_property INGR_MSTR_BRST_WIDTH UNITS None
set_parameter_property INGR_MSTR_BRST_WIDTH HDL_PARAMETER true
set_parameter_property INGR_MSTR_BRST_WIDTH AFFECTS_ELABORATION true
set_parameter_property INGR_MSTR_BRST_WIDTH AFFECTS_GENERATION false
set_parameter_property INGR_MSTR_BRST_WIDTH ENABLED true
set_parameter_property INGR_MSTR_BRST_WIDTH ALLOWED_RANGES { \
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
}

add_parameter EGRS_SLV_ADDR_WIDTH INTEGER 9 "Address width of the egress slave AvMM interface"
set_parameter_property EGRS_SLV_ADDR_WIDTH DISPLAY_NAME "Egress Slave AvMM Address Width"
# set_parameter_property EGRS_SLV_ADDR_WIDTH GROUP ""
set_parameter_property EGRS_SLV_ADDR_WIDTH UNITS None
set_parameter_property EGRS_SLV_ADDR_WIDTH HDL_PARAMETER true
set_parameter_property EGRS_SLV_ADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property EGRS_SLV_ADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property EGRS_SLV_ADDR_WIDTH ENABLED true
set_parameter_property EGRS_SLV_ADDR_WIDTH ALLOWED_RANGES { \
   "6 :6  - 256 Bytes" \
   "7 :7  - 512 Bytes" \
   "8 :8  - 1K Bytes" \
   "9 :9  - 2K Bytes" \
   "10:10 - 4K Bytes" \
   "11:11 - 8K Bytes" \
}

add_parameter SS_ADDR_WIDTH INTEGER 21 "Address width of IOFS FIM sub systems. This will also be used as address width of the egress master AvMM interface"
set_parameter_property SS_ADDR_WIDTH DISPLAY_NAME "IOFS Access Address Width"
# set_parameter_property SS_ADDR_WIDTH GROUP ""
set_parameter_property SS_ADDR_WIDTH UNITS None
set_parameter_property SS_ADDR_WIDTH HDL_PARAMETER true
set_parameter_property SS_ADDR_WIDTH AFFECTS_ELABORATION true
set_parameter_property SS_ADDR_WIDTH AFFECTS_GENERATION false
set_parameter_property SS_ADDR_WIDTH ENABLED true
set_parameter_property SS_ADDR_WIDTH ALLOWED_RANGES {10:32}

add_parameter MCTP_BASELINE_MTU INTEGER 16 "MCTP over PCIe VDM maximum transmission unit size in DWORDs"
set_parameter_property MCTP_BASELINE_MTU DISPLAY_NAME "MCTP over PCIe VDM MTU size in DWORDs"
# set_parameter_property MCTP_BASELINE_MTU GROUP ""
set_parameter_property MCTP_BASELINE_MTU UNITS None
set_parameter_property MCTP_BASELINE_MTU HDL_PARAMETER true
set_parameter_property MCTP_BASELINE_MTU AFFECTS_ELABORATION true
set_parameter_property MCTP_BASELINE_MTU AFFECTS_GENERATION false
set_parameter_property MCTP_BASELINE_MTU ENABLED true
set_parameter_property MCTP_BASELINE_MTU ALLOWED_RANGES {16:128}

add_parameter DEBUG_REG_EN INTEGER 0 "Debug counters and status register implementation enable"
set_parameter_property DEBUG_REG_EN DISPLAY_NAME "Debug register implementation enable"
# set_parameter_property DEBUG_REG_EN GROUP ""
set_parameter_property DEBUG_REG_EN UNITS None
set_parameter_property DEBUG_REG_EN HDL_PARAMETER true
set_parameter_property DEBUG_REG_EN AFFECTS_ELABORATION false
set_parameter_property DEBUG_REG_EN AFFECTS_GENERATION false
set_parameter_property DEBUG_REG_EN ENABLED true
set_parameter_property DEBUG_REG_EN ALLOWED_RANGES { \
   "0:Don't implement debug registers" \
   "1:Implement debug registers" \
}

add_parameter DEBUG_REG_WIDTH INTEGER 8 "Debug counter width"
set_parameter_property DEBUG_REG_WIDTH DISPLAY_NAME "Debug counter width"
# set_parameter_property DEBUG_REG_WIDTH GROUP ""
set_parameter_property DEBUG_REG_WIDTH UNITS None
set_parameter_property DEBUG_REG_WIDTH HDL_PARAMETER true
set_parameter_property DEBUG_REG_WIDTH AFFECTS_ELABORATION false
set_parameter_property DEBUG_REG_WIDTH AFFECTS_GENERATION false
set_parameter_property DEBUG_REG_WIDTH ENABLED true
set_parameter_property DEBUG_REG_WIDTH ALLOWED_RANGES {2:16}

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
# Port - Ingress AvMM Slave
# -----------------------------------------------------------------------------
add_interface avmm_ingr_slv avalon end
set_interface_property avmm_ingr_slv addressUnits WORDS
set_interface_property avmm_ingr_slv associatedClock clock
set_interface_property avmm_ingr_slv associatedReset reset
set_interface_property avmm_ingr_slv bitsPerSymbol 8
set_interface_property avmm_ingr_slv burstOnBurstBoundariesOnly false
set_interface_property avmm_ingr_slv burstcountUnits WORDS
set_interface_property avmm_ingr_slv explicitAddressSpan 0
set_interface_property avmm_ingr_slv holdTime 0
set_interface_property avmm_ingr_slv linewrapBursts false
set_interface_property avmm_ingr_slv maximumPendingReadTransactions 1
set_interface_property avmm_ingr_slv maximumPendingWriteTransactions 0
set_interface_property avmm_ingr_slv readLatency 0
set_interface_property avmm_ingr_slv readWaitTime 1
set_interface_property avmm_ingr_slv setupTime 0
set_interface_property avmm_ingr_slv timingUnits Cycles
set_interface_property avmm_ingr_slv writeWaitTime 0
set_interface_property avmm_ingr_slv ENABLED true
set_interface_property avmm_ingr_slv EXPORT_OF ""
set_interface_property avmm_ingr_slv PORT_NAME_MAP ""
set_interface_property avmm_ingr_slv CMSIS_SVD_VARIABLES ""
set_interface_property avmm_ingr_slv SVD_ADDRESS_GROUP ""

add_interface_port avmm_ingr_slv avmm_ingr_slv_write write Input 1
add_interface_port avmm_ingr_slv avmm_ingr_slv_read read Input 1
add_interface_port avmm_ingr_slv avmm_ingr_slv_addr address Input 1
add_interface_port avmm_ingr_slv avmm_ingr_slv_rddata readdata Output 64
add_interface_port avmm_ingr_slv avmm_ingr_slv_rddvld readdatavalid Output 1
add_interface_port avmm_ingr_slv avmm_ingr_slv_waitreq waitrequest Output 1
add_interface_port avmm_ingr_slv avmm_ingr_slv_wrdata writedata Input 64
add_interface_port avmm_ingr_slv avmm_ingr_slv_byteen byteenable Input 8

# -----------------------------------------------------------------------------
# Port - Ingress AvMM master
# -----------------------------------------------------------------------------
add_interface avmm_ingr_mstr avalon start
set_interface_property avmm_ingr_mstr addressGroup 0
set_interface_property avmm_ingr_mstr addressUnits SYMBOLS
set_interface_property avmm_ingr_mstr associatedClock clock
set_interface_property avmm_ingr_mstr associatedReset reset
set_interface_property avmm_ingr_mstr bitsPerSymbol 8
set_interface_property avmm_ingr_mstr burstOnBurstBoundariesOnly false
set_interface_property avmm_ingr_mstr burstcountUnits WORDS
set_interface_property avmm_ingr_mstr doStreamReads false
set_interface_property avmm_ingr_mstr doStreamWrites false
set_interface_property avmm_ingr_mstr holdTime 0
set_interface_property avmm_ingr_mstr linewrapBursts false
set_interface_property avmm_ingr_mstr maximumPendingReadTransactions 0
set_interface_property avmm_ingr_mstr maximumPendingWriteTransactions 0
set_interface_property avmm_ingr_mstr minimumResponseLatency 1
set_interface_property avmm_ingr_mstr readLatency 0
set_interface_property avmm_ingr_mstr readWaitTime 1
set_interface_property avmm_ingr_mstr setupTime 0
set_interface_property avmm_ingr_mstr timingUnits Cycles
set_interface_property avmm_ingr_mstr waitrequestAllowance 0
set_interface_property avmm_ingr_mstr writeWaitTime 0
set_interface_property avmm_ingr_mstr ENABLED true
set_interface_property avmm_ingr_mstr EXPORT_OF ""
set_interface_property avmm_ingr_mstr PORT_NAME_MAP ""
set_interface_property avmm_ingr_mstr CMSIS_SVD_VARIABLES ""
set_interface_property avmm_ingr_mstr SVD_ADDRESS_GROUP ""
set_interface_property avmm_ingr_mstr IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port avmm_ingr_mstr avmm_ingr_mstr_addr address Output -1
add_interface_port avmm_ingr_mstr avmm_ingr_mstr_write write Output 1
add_interface_port avmm_ingr_mstr avmm_ingr_mstr_read read Output 1
add_interface_port avmm_ingr_mstr avmm_ingr_mstr_burstcnt burstcount Output -1
add_interface_port avmm_ingr_mstr avmm_ingr_mstr_wrdata writedata Output 32
add_interface_port avmm_ingr_mstr avmm_ingr_mstr_rddata readdata Input 32
add_interface_port avmm_ingr_mstr avmm_ingr_mstr_rddvld readdatavalid Input 1
add_interface_port avmm_ingr_mstr avmm_ingr_mstr_waitreq waitrequest Input 1

# -----------------------------------------------------------------------------
# Port - Egress AvMM Slave
# -----------------------------------------------------------------------------
add_interface avmm_egrs_slv avalon end
set_interface_property avmm_egrs_slv addressUnits WORDS
set_interface_property avmm_egrs_slv associatedClock clock
set_interface_property avmm_egrs_slv associatedReset reset
set_interface_property avmm_egrs_slv bitsPerSymbol 8
set_interface_property avmm_egrs_slv burstOnBurstBoundariesOnly false
set_interface_property avmm_egrs_slv burstcountUnits WORDS
set_interface_property avmm_egrs_slv explicitAddressSpan 0
set_interface_property avmm_egrs_slv holdTime 0
set_interface_property avmm_egrs_slv linewrapBursts false
set_interface_property avmm_egrs_slv maximumPendingReadTransactions 1
set_interface_property avmm_egrs_slv maximumPendingWriteTransactions 0
set_interface_property avmm_egrs_slv readLatency 0
set_interface_property avmm_egrs_slv readWaitTime 1
set_interface_property avmm_egrs_slv setupTime 0
set_interface_property avmm_egrs_slv timingUnits Cycles
set_interface_property avmm_egrs_slv writeWaitTime 0
set_interface_property avmm_egrs_slv ENABLED true
set_interface_property avmm_egrs_slv EXPORT_OF ""
set_interface_property avmm_egrs_slv PORT_NAME_MAP ""
set_interface_property avmm_egrs_slv CMSIS_SVD_VARIABLES ""
set_interface_property avmm_egrs_slv SVD_ADDRESS_GROUP ""

add_interface_port avmm_egrs_slv avmm_egrs_slv_write write Input 1
add_interface_port avmm_egrs_slv avmm_egrs_slv_read read Input 1
add_interface_port avmm_egrs_slv avmm_egrs_slv_addr address Input -1
add_interface_port avmm_egrs_slv avmm_egrs_slv_rddata readdata Output 32
add_interface_port avmm_egrs_slv avmm_egrs_slv_rddvld readdatavalid Output 1
add_interface_port avmm_egrs_slv avmm_egrs_slv_waitreq waitrequest Output 1
add_interface_port avmm_egrs_slv avmm_egrs_slv_wrdata writedata Input 32


# -----------------------------------------------------------------------------
# Port - Egress AvMM master
# -----------------------------------------------------------------------------
add_interface avmm_egrs_mstr avalon start
set_interface_property avmm_egrs_mstr addressGroup 0
set_interface_property avmm_egrs_mstr addressUnits SYMBOLS
set_interface_property avmm_egrs_mstr associatedClock clock
set_interface_property avmm_egrs_mstr associatedReset reset
set_interface_property avmm_egrs_mstr bitsPerSymbol 8
set_interface_property avmm_egrs_mstr burstOnBurstBoundariesOnly false
set_interface_property avmm_egrs_mstr burstcountUnits WORDS
set_interface_property avmm_egrs_mstr doStreamReads false
set_interface_property avmm_egrs_mstr doStreamWrites false
set_interface_property avmm_egrs_mstr holdTime 0
set_interface_property avmm_egrs_mstr linewrapBursts false
set_interface_property avmm_egrs_mstr maximumPendingReadTransactions 0
set_interface_property avmm_egrs_mstr maximumPendingWriteTransactions 0
set_interface_property avmm_egrs_mstr minimumResponseLatency 1
set_interface_property avmm_egrs_mstr readLatency 0
set_interface_property avmm_egrs_mstr readWaitTime 1
set_interface_property avmm_egrs_mstr setupTime 0
set_interface_property avmm_egrs_mstr timingUnits Cycles
set_interface_property avmm_egrs_mstr waitrequestAllowance 0
set_interface_property avmm_egrs_mstr writeWaitTime 0
set_interface_property avmm_egrs_mstr ENABLED true
set_interface_property avmm_egrs_mstr EXPORT_OF ""
set_interface_property avmm_egrs_mstr PORT_NAME_MAP ""
set_interface_property avmm_egrs_mstr CMSIS_SVD_VARIABLES ""
set_interface_property avmm_egrs_mstr SVD_ADDRESS_GROUP ""
set_interface_property avmm_egrs_mstr IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port avmm_egrs_mstr avmm_egrs_mstr_addr address Output -1
add_interface_port avmm_egrs_mstr avmm_egrs_mstr_write write Output 1
add_interface_port avmm_egrs_mstr avmm_egrs_mstr_read read Output 1
add_interface_port avmm_egrs_mstr avmm_egrs_mstr_wrdata writedata Output 64
add_interface_port avmm_egrs_mstr avmm_egrs_mstr_byteen byteenable Output 8
add_interface_port avmm_egrs_mstr avmm_egrs_mstr_rddata readdata Input 64
add_interface_port avmm_egrs_mstr avmm_egrs_mstr_rddvld readdatavalid Input 1
add_interface_port avmm_egrs_mstr avmm_egrs_mstr_waitreq waitrequest Input 1

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

add_interface_port csr_if pcievdm_afu_addr pcievdm_afu_addr Input -1
add_interface_port csr_if pcievdm_afu_addr_vld pcievdm_afu_addr_vld Input 1
add_interface_port csr_if pcievdm_mctp_eid pcievdm_mctp_eid Input 8
add_interface_port csr_if pcie_vdm_sts1_dbg pcie_vdm_sts1_dbg Output 64
add_interface_port csr_if pcie_vdm_sts2_dbg pcie_vdm_sts2_dbg Output 64
add_interface_port csr_if pcie_vdm_sts3_dbg pcie_vdm_sts3_dbg Output 64
add_interface_port csr_if pcie_vdm_sts4_dbg pcie_vdm_sts4_dbg Output 64
add_interface_port csr_if pcie_vdm_sts5_dbg pcie_vdm_sts5_dbg Output 64

# -----------------------------------------------------------------------------
# Validate IP
# -----------------------------------------------------------------------------
proc ip_validate { } {
   
   set ingrm_awidth [ get_parameter_value INGR_MSTR_ADDR_WIDTH ]
   set ingrm_bwidth [ get_parameter_value INGR_MSTR_BRST_WIDTH ]
#  set egrss_awidth [ get_parameter_value EGRS_SLV_ADDR_WIDTH ]
#  set egrsm_awidth [ get_parameter_value SS_ADDR_WIDTH ]

   set addr_span  [expr {pow(2, $ingrm_awidth)}]
   set max_bcount [expr {2 * pow(2, $ingrm_bwidth)}]
   
   if { $max_bcount > $addr_span } {
            send_message Error "Addressable bytes are lesser than maximum burst length"
            send_message Info "Address width spans $addr_span bytes."
            send_message Info "Maximum burst count is $max_bcount bytes."
   }
}

# -----------------------------------------------------------------------------
# Elaborate IP
# -----------------------------------------------------------------------------
proc ip_elaborate { } {
   
   set ingrm_awidth [ get_parameter_value INGR_MSTR_ADDR_WIDTH ]
   set ingrm_bwidth [ get_parameter_value INGR_MSTR_BRST_WIDTH ]
   set egrss_awidth [ get_parameter_value EGRS_SLV_ADDR_WIDTH ]
   set egrsm_awidth [ get_parameter_value SS_ADDR_WIDTH ]
   
   set_port_property avmm_ingr_mstr_addr     width_expr $ingrm_awidth
   set_port_property avmm_ingr_mstr_burstcnt width_expr $ingrm_bwidth
   set_port_property avmm_egrs_slv_addr      width_expr $egrss_awidth
   set_port_property avmm_egrs_mstr_addr     width_expr $egrsm_awidth
   set_port_property pcievdm_afu_addr        width_expr $egrsm_awidth
}
