# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

# 
# Description
# -----------------------------------------------------------------------------
# This is the _hw.tcl of NCSI Controller
# -----------------------------------------------------------------------------


# -----------------------------------------------------------------------------
# Module Properties
# -----------------------------------------------------------------------------
package require -exact qsys 20.3

set_module_property DESCRIPTION "NCSI Controller IP"
set_module_property NAME ncsi_ctrlr
set_module_property VERSION 1.0
set_module_property GROUP "PMCI-SS Custom IP"
set_module_property DISPLAY_NAME "NCSI Controller"
set_module_property INSTANTIATE_IN_SYSTEM_MODULE true
set_module_property EDITABLE true
# set_module_property INTERNAL false
# set_module_property OPAQUE_ADDRESS_MAP true

# -----------------------------------------------------------------------------
# Files
# -----------------------------------------------------------------------------
add_fileset synth_fileset QUARTUS_SYNTH synth_callback_procedure
set_fileset_property synth_fileset TOP_LEVEL ncsi_ctrlr
# set_fileset_property synth_fileset ENABLE_RELATIVE_INCLUDE_PATHS false
# set_fileset_property synth_fileset ENABLE_FILE_OVERWRITE_MODE false
add_fileset simver_fileset SIM_VERILOG synth_callback_procedure
set_fileset_property simver_fileset TOP_LEVEL ncsi_ctrlr
add_fileset simvhd_fileset SIM_VHDL synth_callback_procedure
set_fileset_property simvhd_fileset TOP_LEVEL ncsi_ctrlr

# proc synth_callback_procedure { } {
proc synth_callback_procedure { entity_name } {
   add_fileset_file ncsi_ctrlr.sv SYSTEM_VERILOG PATH "./custom_ip/ncsi_ctrlr/ncsi_ctrlr.sv" TOP_LEVEL_FILE
}


# -----------------------------------------------------------------------------
# Parameters
# -----------------------------------------------------------------------------

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
# Port - RBT interface (conduit)
# -----------------------------------------------------------------------------
add_interface ncsi_rbt_if conduit end
set_interface_property ncsi_rbt_if associatedClock clock
set_interface_property ncsi_rbt_if associatedReset reset
set_interface_property ncsi_rbt_if ENABLED true
set_interface_property ncsi_rbt_if EXPORT_OF ""
set_interface_property ncsi_rbt_if PORT_NAME_MAP ""
set_interface_property ncsi_rbt_if CMSIS_SVD_VARIABLES ""
set_interface_property ncsi_rbt_if SVD_ADDRESS_GROUP ""
set_interface_property ncsi_rbt_if IPXACT_REGISTER_MAP_VARIABLES ""

add_interface_port ncsi_rbt_if ncsi_clk ncsi_clk Input 1
add_interface_port ncsi_rbt_if ncsi_txd ncsi_txd Input 2
add_interface_port ncsi_rbt_if ncsi_tx_en ncsi_tx_en Input 1
add_interface_port ncsi_rbt_if ncsi_rxd ncsi_rxd Output 2
add_interface_port ncsi_rbt_if ncsi_crs_dv ncsi_crs_dv Output 1
add_interface_port ncsi_rbt_if ncsi_arb_in ncsi_arb_in Input 1
add_interface_port ncsi_rbt_if ncsi_arb_out ncsi_arb_out Output 1
