package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

proc do_adjust_ftile_mr_eth_ip_1x100g {} {
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P10_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P11_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P12_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P13_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P14_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P15_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P16_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P17_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P18_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P19_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P1_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P20_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P21_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P22_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P23_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P24_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P25_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P26_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P27_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P28_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P29_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P2_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P30_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P31_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P32_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P3_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P4_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P5_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P6_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P7_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P8_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P9_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {RCFG_GRP_GUI} {100G-4}
	set_instance_parameter_value eth_f_dr_0 {RSFEC_TYPE_P0_GUI} {2}
	set_instance_parameter_value eth_f_dr_0 {START_PROF_GUI} {1x100GE-4}
	
	set_interface_property o_p1_clk_tx_div EXPORT_OF eth_f_dr_0.o_p1_clk_tx_div
	set_interface_property o_p1_clk_rec_div64 EXPORT_OF eth_f_dr_0.o_p1_clk_rec_div64
	set_interface_property o_p1_clk_rec_div EXPORT_OF eth_f_dr_0.o_p1_clk_rec_div
	set_interface_property i_p1_rst_n EXPORT_OF eth_f_dr_0.i_p1_rst_n
	set_interface_property i_p1_tx_rst_n EXPORT_OF eth_f_dr_0.i_p1_tx_rst_n
	set_interface_property i_p1_rx_rst_n EXPORT_OF eth_f_dr_0.i_p1_rx_rst_n
	set_interface_property o_p1_rst_ack_n EXPORT_OF eth_f_dr_0.o_p1_rst_ack_n
	set_interface_property o_p1_rx_rst_ack_n EXPORT_OF eth_f_dr_0.o_p1_rx_rst_ack_n
	set_interface_property o_p1_tx_rst_ack_n EXPORT_OF eth_f_dr_0.o_p1_tx_rst_ack_n
	set_interface_property o_p1_tx_pll_locked EXPORT_OF eth_f_dr_0.o_p1_tx_pll_locked
	set_interface_property o_p1_cdr_lock EXPORT_OF eth_f_dr_0.o_p1_cdr_lock
	set_interface_property o_p1_tx_lanes_stable EXPORT_OF eth_f_dr_0.o_p1_tx_lanes_stable
	set_interface_property o_p1_rx_pcs_ready EXPORT_OF eth_f_dr_0.o_p1_rx_pcs_ready
	set_interface_property p1_pfc_ports EXPORT_OF eth_f_dr_0.p1_pfc_ports
	set_interface_property p1_status_ports EXPORT_OF eth_f_dr_0.p1_status_ports
	set_interface_property p1_reconfig_eth_slave EXPORT_OF eth_f_dr_0.p1_reconfig_eth_slave
	set_interface_property o_p2_clk_tx_div EXPORT_OF eth_f_dr_0.o_p2_clk_tx_div
	set_interface_property o_p2_clk_rec_div64 EXPORT_OF eth_f_dr_0.o_p2_clk_rec_div64
	set_interface_property o_p2_clk_rec_div EXPORT_OF eth_f_dr_0.o_p2_clk_rec_div
	set_interface_property i_p2_rst_n EXPORT_OF eth_f_dr_0.i_p2_rst_n
	set_interface_property i_p2_tx_rst_n EXPORT_OF eth_f_dr_0.i_p2_tx_rst_n
	set_interface_property i_p2_rx_rst_n EXPORT_OF eth_f_dr_0.i_p2_rx_rst_n
	set_interface_property o_p2_rst_ack_n EXPORT_OF eth_f_dr_0.o_p2_rst_ack_n
	set_interface_property o_p2_rx_rst_ack_n EXPORT_OF eth_f_dr_0.o_p2_rx_rst_ack_n
	set_interface_property o_p2_tx_rst_ack_n EXPORT_OF eth_f_dr_0.o_p2_tx_rst_ack_n
	set_interface_property o_p2_tx_pll_locked EXPORT_OF eth_f_dr_0.o_p2_tx_pll_locked
	set_interface_property o_p2_cdr_lock EXPORT_OF eth_f_dr_0.o_p2_cdr_lock
	set_interface_property o_p2_tx_lanes_stable EXPORT_OF eth_f_dr_0.o_p2_tx_lanes_stable
	set_interface_property o_p2_rx_pcs_ready EXPORT_OF eth_f_dr_0.o_p2_rx_pcs_ready
	set_interface_property p2_pfc_ports EXPORT_OF eth_f_dr_0.p2_pfc_ports
	set_interface_property p2_status_ports EXPORT_OF eth_f_dr_0.p2_status_ports
	set_interface_property p2_reconfig_eth_slave EXPORT_OF eth_f_dr_0.p2_reconfig_eth_slave
	set_interface_property o_p3_clk_tx_div EXPORT_OF eth_f_dr_0.o_p3_clk_tx_div
	set_interface_property o_p3_clk_rec_div64 EXPORT_OF eth_f_dr_0.o_p3_clk_rec_div64
	set_interface_property o_p3_clk_rec_div EXPORT_OF eth_f_dr_0.o_p3_clk_rec_div
	set_interface_property i_p3_rst_n EXPORT_OF eth_f_dr_0.i_p3_rst_n
	set_interface_property i_p3_tx_rst_n EXPORT_OF eth_f_dr_0.i_p3_tx_rst_n
	set_interface_property i_p3_rx_rst_n EXPORT_OF eth_f_dr_0.i_p3_rx_rst_n
	set_interface_property o_p3_rst_ack_n EXPORT_OF eth_f_dr_0.o_p3_rst_ack_n
	set_interface_property o_p3_rx_rst_ack_n EXPORT_OF eth_f_dr_0.o_p3_rx_rst_ack_n
	set_interface_property o_p3_tx_rst_ack_n EXPORT_OF eth_f_dr_0.o_p3_tx_rst_ack_n
	set_interface_property o_p3_tx_pll_locked EXPORT_OF eth_f_dr_0.o_p3_tx_pll_locked
	set_interface_property o_p3_cdr_lock EXPORT_OF eth_f_dr_0.o_p3_cdr_lock
	set_interface_property o_p3_tx_lanes_stable EXPORT_OF eth_f_dr_0.o_p3_tx_lanes_stable
	set_interface_property o_p3_rx_pcs_ready EXPORT_OF eth_f_dr_0.o_p3_rx_pcs_ready
	set_interface_property p3_pfc_ports EXPORT_OF eth_f_dr_0.p3_pfc_ports
	set_interface_property p3_status_ports EXPORT_OF eth_f_dr_0.p3_status_ports
	set_interface_property p3_reconfig_eth_slave EXPORT_OF eth_f_dr_0.p3_reconfig_eth_slave
	set_interface_property p1_ptp_clk_tx_tod EXPORT_OF eth_f_dr_0.p1_ptp_clk_tx_tod
	set_interface_property p1_ptp_clk_rx_tod EXPORT_OF eth_f_dr_0.p1_ptp_clk_rx_tod
	set_interface_property p2_ptp_clk_tx_tod EXPORT_OF eth_f_dr_0.p2_ptp_clk_tx_tod
	set_interface_property p2_ptp_clk_rx_tod EXPORT_OF eth_f_dr_0.p2_ptp_clk_rx_tod
	set_interface_property p3_ptp_clk_tx_tod EXPORT_OF eth_f_dr_0.p3_ptp_clk_tx_tod
	set_interface_property p3_ptp_clk_rx_tod EXPORT_OF eth_f_dr_0.p3_ptp_clk_rx_tod
	set_interface_property reconfig_xcvr_slave_1 EXPORT_OF eth_f_dr_0.reconfig_xcvr_slave_1
	set_interface_property reconfig_xcvr_slave_2 EXPORT_OF eth_f_dr_0.reconfig_xcvr_slave_2
	set_interface_property reconfig_xcvr_slave_3 EXPORT_OF eth_f_dr_0.reconfig_xcvr_slave_3
}

proc do_adjust_ftile_mr_eth_ip_1x25g_1x10g {} {
	set_instance_parameter_value eth_f_dr_0 {ETH_MODE_P3_GUI} {10G-1}
	set_instance_parameter_value eth_f_dr_0 {MAC_P0_COPY_P2_GUI} {1}
	set_instance_parameter_value eth_f_dr_0 {MAC_P0_COPY_P3_GUI} {1}
	set_instance_parameter_value eth_f_dr_0 {NUM_SEC_PROFILE_GUI} {3}
	set_instance_parameter_value eth_f_dr_0 {RSFEC_TYPE_P1_GUI} {2}
	set_instance_parameter_value eth_f_dr_0 {RSFEC_TYPE_P2_GUI} {3}
	set_instance_parameter_value eth_f_dr_0 {p2_enforce_max_frame_size_gui} {1}
	set_instance_parameter_value eth_f_dr_0 {p2_link_fault_mode_gui} {Bidirectional}
	set_instance_parameter_value eth_f_dr_0 {p2_rx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p2_rx_vlan_detection_gui} {0}
	set_instance_parameter_value eth_f_dr_0 {p2_tx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p2_tx_vlan_detection_gui} {0}
	set_instance_parameter_value eth_f_dr_0 {p3_enforce_max_frame_size_gui} {1}
	set_instance_parameter_value eth_f_dr_0 {p3_link_fault_mode_gui} {Bidirectional}
	set_instance_parameter_value eth_f_dr_0 {p3_rx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p3_rx_vlan_detection_gui} {0}
	set_instance_parameter_value eth_f_dr_0 {p3_tx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p3_tx_vlan_detection_gui} {0}
}

# adjust parameters in "ftile_mr_eth_ip" system
proc do_adjust_ftile_mr_eth_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	# common IP core parameters
	set_instance_parameter_value eth_f_dr_0 {MAC_P0_COPY_P1_GUI} {1}
	set_instance_parameter_value eth_f_dr_0 {SYSPLL_RATE_GUI} {1}
	set_instance_parameter_value eth_f_dr_0 {p0_enforce_max_frame_size_gui} {1}
	set_instance_parameter_value eth_f_dr_0 {p0_link_fault_mode_gui} {Bidirectional}
	set_instance_parameter_value eth_f_dr_0 {p0_rx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p0_rx_vlan_detection_gui} {0}
	set_instance_parameter_value eth_f_dr_0 {p0_tx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p0_tx_vlan_detection_gui} {0}
        set_instance_parameter_value eth_f_dr_0 {p1_enforce_max_frame_size_gui} {1}
	set_instance_parameter_value eth_f_dr_0 {p1_link_fault_mode_gui} {Bidirectional}
	set_instance_parameter_value eth_f_dr_0 {p1_rx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p1_rx_vlan_detection_gui} {0}
	set_instance_parameter_value eth_f_dr_0 {p1_tx_max_frame_size_gui} {16383}
	set_instance_parameter_value eth_f_dr_0 {p1_tx_vlan_detection_gui} {0}

	# configuration-specific parameters
	$adjust_proc

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(ETH_PORT_SPEED,0) == 100} {
	set cb do_adjust_ftile_mr_eth_ip_1x100g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 25} {
	set cb do_adjust_ftile_mr_eth_ip_1x25g_1x10g
}

do_adjust_ftile_mr_eth_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
