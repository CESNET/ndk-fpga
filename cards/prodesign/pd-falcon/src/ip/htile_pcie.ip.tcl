# htile_pcie.ip.tcl: TCL script for generating the H-Tile PCIe IP
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

load_system $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
set_project_property DEVICE $PARAMS(IP_DEVICE)
set_project_property DEVICE_FAMILY $PARAMS(IP_DEVICE_FAMILY)
set_project_property HIDE_FROM_IP_CATALOG {true}

set_instance_parameter_value pcie_s10_hip_ast_0 {wrala_hwtcl} {Gen3x16, Interface - 512 bit, 250 MHz}
set_instance_parameter_value pcie_s10_hip_ast_0 {cvp_user_id_hwtcl} {3451}
set_instance_parameter_value pcie_s10_hip_ast_0 {pf0_pci_type0_vendor_id_hwtcl} {6380}
set_instance_parameter_value pcie_s10_hip_ast_0 {pf0_pci_type0_device_id_hwtcl} {49152}
set_instance_parameter_value pcie_s10_hip_ast_0 {pf0_class_code_hwtcl} {131072}
set_instance_parameter_value pcie_s10_hip_ast_0 {pf0_bar0_type_hwtcl} {32-bit non-prefetchable memory}
set_instance_parameter_value pcie_s10_hip_ast_0 {pf0_bar0_address_width_hwtcl} {26}
set_instance_parameter_value pcie_s10_hip_ast_0 {pf0_pcie_cap_ext_tag_supp_hwtcl} {1}
set_instance_parameter_value pcie_s10_hip_ast_0 {pf0_pcie_cap_flr_cap_user_hwtcl} {0}

# The IP enables the VSEC also on PF1-PF3, htile_pcie_fix.sh disables it.
set_instance_parameter_value pcie_s10_hip_ast_0 {ceb_extend_pcie_hwtcl} {1}

save_system $PARAMS(IP_COMP_NAME)
