# ftile_eth.ip.tcl: TCL script for generating Ethernet F-Tile.
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

proc do_adjust_ftile_eth_ip_1x400g {} {
	set_instance_parameter_value eth_f_0 {BASE_SEC_ENABLE} {0}
	set_instance_parameter_value eth_f_0 {CUSTOM_RATE_GUI} {25.78125}
	set_instance_parameter_value eth_f_0 {ENABLE_ADME_GUI} {1}
	set_instance_parameter_value eth_f_0 {ENABLE_IPXACT_GUI} {1}
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {400G-8}
	set_instance_parameter_value eth_f_0 {OPTIMIZED_SIM_ENABLE} {0}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {1}
	set_instance_parameter_value eth_f_0 {QUARTUS_CDC} {0}
	set_instance_parameter_value eth_f_0 {RSFEC_TYPE_GUI} {3}
	set_instance_parameter_value eth_f_0 {SIM_TIME} {0}
	set_instance_parameter_value eth_f_0 {bk_cfg_kvcc_vreg_offset_en_val} {CFG_KVCC_VREG_OFFSET_EN_VAL_DISABLE}
	set_instance_parameter_value eth_f_0 {bk_ext_ac_cap} {EXTERNAL_AC_CAP_ENABLE}
	set_instance_parameter_value eth_f_0 {bk_rx_invert_p_and_n} {RX_INVERT_PN_DIS}
	set_instance_parameter_value eth_f_0 {bk_rx_termination} {RXTERM_OFFSET_P0}
	set_instance_parameter_value eth_f_0 {bk_tx_invert_p_and_n} {TX_INVERT_PN_DIS}
	set_instance_parameter_value eth_f_0 {bk_tx_termination} {TXTERM_OFFSET_P0}
	set_instance_parameter_value eth_f_0 {bk_txeq_main_tap} {41.5}
	set_instance_parameter_value eth_f_0 {bk_txeq_post_tap_1} {0.0}
	set_instance_parameter_value eth_f_0 {bk_txeq_post_tap_2} {0.0}
	set_instance_parameter_value eth_f_0 {bk_txeq_post_tap_3} {0.0}
	set_instance_parameter_value eth_f_0 {bk_txeq_post_tap_4} {0.0}
	set_instance_parameter_value eth_f_0 {bk_txeq_pre_tap_1} {0.0}
	set_instance_parameter_value eth_f_0 {bk_txeq_pre_tap_2} {0.0}
	set_instance_parameter_value eth_f_0 {bk_txeq_pre_tap_3} {0.0}
	set_instance_parameter_value eth_f_0 {bk_txout_tristate_en} {TXOUT_TRISTATE_DIS}
	set_instance_parameter_value eth_f_0 {debug_counter} {0}
	set_instance_parameter_value eth_f_0 {fgt_protocol_mode} {DISABLED}
	set_instance_parameter_value eth_f_0 {protocol_hard_pcie_lowloss} {DISABLE}
	set_instance_parameter_value eth_f_0 {rx_ac_couple_enable} {ENABLE}
	set_instance_parameter_value eth_f_0 {rx_onchip_termination} {RX_ONCHIP_TERMINATION_R_2}
	set_instance_parameter_value eth_f_0 {rxeq_dfe_data_tap_1} {0}
	set_instance_parameter_value eth_f_0 {rxeq_hf_boost} {0}
	set_instance_parameter_value eth_f_0 {rxeq_vga_gain} {0}
	set_instance_parameter_value eth_f_0 {txmac_saddr_gui} {001122334455}
	set_instance_parameter_value eth_f_0 {ux_txeq_main_tap} {35}
	set_instance_parameter_value eth_f_0 {ux_txeq_post_tap_1} {0}
	set_instance_parameter_value eth_f_0 {ux_txeq_pre_tap_1} {5}
	set_instance_parameter_value eth_f_0 {ux_txeq_pre_tap_2} {0}
	set_instance_parameter_value eth_f_0 {vsr_mode} {VSR_MODE_DISABLE}

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
