package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

proc do_adjust_ftile_eth_ip_1x400g {} {
	set_instance_parameter_value eth_f_0 {ENABLE_ADME_GUI} {1}
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {400G-8}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {1}
	set_instance_parameter_value eth_f_0 {RSFEC_TYPE_GUI} {3}

	set_interface_property reconfig_xcvr_slave_1 EXPORT_OF eth_f_0.reconfig_xcvr_slave_1
	set_interface_property reconfig_xcvr_slave_2 EXPORT_OF eth_f_0.reconfig_xcvr_slave_2
	set_interface_property reconfig_xcvr_slave_3 EXPORT_OF eth_f_0.reconfig_xcvr_slave_3
	set_interface_property reconfig_xcvr_slave_4 EXPORT_OF eth_f_0.reconfig_xcvr_slave_4
	set_interface_property reconfig_xcvr_slave_5 EXPORT_OF eth_f_0.reconfig_xcvr_slave_5
	set_interface_property reconfig_xcvr_slave_6 EXPORT_OF eth_f_0.reconfig_xcvr_slave_6
	set_interface_property reconfig_xcvr_slave_7 EXPORT_OF eth_f_0.reconfig_xcvr_slave_7
}

proc do_adjust_ftile_eth_ip_2x200g {} {
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {200G-4}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {1}
	set_instance_parameter_value eth_f_0 {RSFEC_TYPE_GUI} {3}

	set_interface_property reconfig_xcvr_slave_1 EXPORT_OF eth_f_0.reconfig_xcvr_slave_1
	set_interface_property reconfig_xcvr_slave_2 EXPORT_OF eth_f_0.reconfig_xcvr_slave_2
	set_interface_property reconfig_xcvr_slave_3 EXPORT_OF eth_f_0.reconfig_xcvr_slave_3
}

proc do_adjust_ftile_eth_ip_4x100g {} {
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {100G-2}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {1}
	set_instance_parameter_value eth_f_0 {RSFEC_TYPE_GUI} {3}

	set_interface_property reconfig_xcvr_slave_1 EXPORT_OF eth_f_0.reconfig_xcvr_slave_1
}

proc do_adjust_ftile_eth_ip_2x100g {} {
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {100G-4}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {1}

	set_interface_property reconfig_xcvr_slave_1 EXPORT_OF eth_f_0.reconfig_xcvr_slave_1
	set_interface_property reconfig_xcvr_slave_2 EXPORT_OF eth_f_0.reconfig_xcvr_slave_2
	set_interface_property reconfig_xcvr_slave_3 EXPORT_OF eth_f_0.reconfig_xcvr_slave_3
}

proc do_adjust_ftile_eth_ip_8x50g {} {
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {50G-1}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {1}
	set_instance_parameter_value eth_f_0 {RSFEC_TYPE_GUI} {3}
}

proc do_adjust_ftile_eth_ip_2x40g {} {
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {40G-4}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {1}

	set_interface_property reconfig_xcvr_slave_1 EXPORT_OF eth_f_0.reconfig_xcvr_slave_1
	set_interface_property reconfig_xcvr_slave_2 EXPORT_OF eth_f_0.reconfig_xcvr_slave_2
	set_interface_property reconfig_xcvr_slave_3 EXPORT_OF eth_f_0.reconfig_xcvr_slave_3
}

proc do_adjust_ftile_eth_ip_8x25g {} {
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {25G-1}
	set_instance_parameter_value eth_f_0 {RSFEC_TYPE_GUI} {2}
}

proc do_adjust_ftile_eth_ip_8x10g {} {
}


# adjust parameters in "ftile_eth_ip" system
proc do_adjust_ftile_eth_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	# common IP core parameters
	set_instance_parameter_value eth_f_0 {DV_OVERRIDE} {1}
	set_instance_parameter_value eth_f_0 {ENABLE_ETK_GUI} {1}
	set_instance_parameter_value eth_f_0 {SYSPLL_RATE_GUI} {1}
	set_instance_parameter_value eth_f_0 {enforce_max_frame_size_gui} {1}
	set_instance_parameter_value eth_f_0 {link_fault_mode_gui} {Bidirectional}
	set_instance_parameter_value eth_f_0 {rx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_0 {rx_vlan_detection_gui} {0}
	set_instance_parameter_value eth_f_0 {tx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_0 {tx_vlan_detection_gui} {0}

	# configuration-specific parameters
	$adjust_proc

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(ETH_PORT_SPEED,0) == 400} {
	set cb do_adjust_ftile_eth_ip_1x400g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 200} {
	set cb do_adjust_ftile_eth_ip_2x200g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 100 && $PARAMS(ETH_PORT_CHAN,0) == 4} {
	set cb do_adjust_ftile_eth_ip_4x100g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 100 && $PARAMS(ETH_PORT_CHAN,0) == 2} {
	set cb do_adjust_ftile_eth_ip_2x100g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 50} {
	set cb do_adjust_ftile_eth_ip_8x50g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 40} {
	set cb do_adjust_ftile_eth_ip_2x40g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 25} {
	set cb do_adjust_ftile_eth_ip_8x25g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 10} {
	set cb do_adjust_ftile_eth_ip_8x10g
}

do_adjust_ftile_eth_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
