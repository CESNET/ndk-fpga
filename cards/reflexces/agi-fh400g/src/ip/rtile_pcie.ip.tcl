package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

proc do_adjust_rtile_pcie_ip_1x16 {} {
}

proc do_adjust_rtile_pcie_ip_2x8 {} {
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_gen2_ctrl_off_support_mod_ts_hwtcl} {0}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core4_0_pf0_gen2_ctrl_off_support_mod_ts_hwtcl} {0}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core4_1_pf0_gen2_ctrl_off_support_mod_ts_hwtcl} {0}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cap_slot_clk_config_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cii_range_0_k_cii_addr_size0_attr_user_hwtcl} {767}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cii_range_0_k_cii_pf_en0_attr_user_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cii_range_0_k_cii_start_addr0_attr_user_hwtcl} {3328}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_enable_cii_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_bar0_address_width_user_hwtcl} {26}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_bar0_type_user_hwtcl} {64-bit non-prefetchable memory}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_class_code_hwtcl} {131072}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_gen2_ctrl_off_support_mod_ts_hwtcl} {0}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_pci_type0_device_id_hwtcl} {50176}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_pci_type0_vendor_id_user_hwtcl} {6380}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_user_vsec_cap_enable_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_virtual_pf0_user_vsec_offset_hwtcl} {3328}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {design_environment} {Unknown}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {standard_interface_selection_hwtcl} {0}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {top_topology_hwtcl} {Gen5 2x8, Interface - 512 bit}

	set_interface_property p1_rx_st0 EXPORT_OF intel_rtile_pcie_ast_0.p1_rx_st0
	set_interface_property p1_rx_st_misc EXPORT_OF intel_rtile_pcie_ast_0.p1_rx_st_misc
	set_interface_property p1_rx_st1 EXPORT_OF intel_rtile_pcie_ast_0.p1_rx_st1
	set_interface_property p1_tx_st_misc EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_st_misc
	set_interface_property p1_tx_st0 EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_st0
	set_interface_property p1_tx_st1 EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_st1
	set_interface_property p1_tx_ehp EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_ehp
	set_interface_property p1_reset_status_n EXPORT_OF intel_rtile_pcie_ast_0.p1_reset_status_n
	set_interface_property p1_slow_reset_status_n EXPORT_OF intel_rtile_pcie_ast_0.p1_slow_reset_status_n
	set_interface_property p1_hip_status EXPORT_OF intel_rtile_pcie_ast_0.p1_hip_status
	set_interface_property p1_power_mgnt EXPORT_OF intel_rtile_pcie_ast_0.p1_power_mgnt
	set_interface_property p1_pld_gp EXPORT_OF intel_rtile_pcie_ast_0.p1_pld_gp
	set_interface_property p1_cii EXPORT_OF intel_rtile_pcie_ast_0.p1_cii
}

# adjust parameters in "rtile_pcie_ip" system
proc do_adjust_rtile_pcie_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	# common IP core parameters
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cap_slot_clk_config_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cii_range_0_k_cii_addr_size0_attr_user_hwtcl} {767}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cii_range_0_k_cii_pf_en0_attr_user_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cii_range_0_k_cii_start_addr0_attr_user_hwtcl} {3328}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_enable_cii_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_bar0_address_width_user_hwtcl} {26}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_bar0_type_user_hwtcl} {64-bit non-prefetchable memory}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_class_code_hwtcl} {131072}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_pci_type0_device_id_hwtcl} {50176}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_pci_type0_vendor_id_user_hwtcl} {6380}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_user_vsec_cap_enable_hwtcl} {1}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_virtual_pf0_user_vsec_offset_hwtcl} {3328}
	set_instance_parameter_value intel_rtile_pcie_ast_0 {g5_pld_clkfreq_user_hwtcl} {400MHz}

	# configuration-specific parameters
	$adjust_proc

	set_interface_property p0_cii EXPORT_OF intel_rtile_pcie_ast_0.p0_cii

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(PCIE_ENDPOINT_MODE) == 0} {
	set cb do_adjust_rtile_pcie_ip_1x16
} elseif {$PARAMS(PCIE_ENDPOINT_MODE) == 1} {
	set cb do_adjust_rtile_pcie_ip_2x8
}

do_adjust_rtile_pcie_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
