package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

proc do_adjust_etile_eth_ip_1x100g {} {
	set_instance_parameter_value alt_ehipc3_fm_0 {ENABLE_RSFEC} {1}
	set_instance_parameter_value alt_ehipc3_fm_0 {core_variant} {2}
	set_instance_parameter_value alt_ehipc3_fm_0 {ehip_mode_gui} {MAC+PCS+(528,514)RSFEC}
	set_instance_parameter_value alt_ehipc3_fm_0 {ehip_mode_gui_sl_0} {MAC+PCS+RSFEC}
	set_instance_parameter_value alt_ehipc3_fm_0 {flow_control_gui} {Disable Flow Control}
	set_instance_parameter_value alt_ehipc3_fm_0 {link_fault_mode_gui} {OFF}
	set_instance_parameter_value alt_ehipc3_fm_0 {rcp_load_enable} {1}
	set_instance_parameter_value alt_ehipc3_fm_0 {rx_max_frame_size_gui} {16383}
	set_instance_parameter_value alt_ehipc3_fm_0 {rx_vlan_detection_gui} {0}
	set_instance_parameter_value alt_ehipc3_fm_0 {tx_max_frame_size_gui} {16383}
	set_instance_parameter_value alt_ehipc3_fm_0 {tx_vlan_detection_gui} {0}

	set_interface_property i_stats_snapshot EXPORT_OF alt_ehipc3_fm_0.i_stats_snapshot
	set_interface_property eth_reconfig EXPORT_OF alt_ehipc3_fm_0.eth_reconfig
	set_interface_property rsfec_reconfig EXPORT_OF alt_ehipc3_fm_0.rsfec_reconfig
	set_interface_property o_tx_lanes_stable EXPORT_OF alt_ehipc3_fm_0.o_tx_lanes_stable
	set_interface_property o_rx_pcs_ready EXPORT_OF alt_ehipc3_fm_0.o_rx_pcs_ready
	set_interface_property o_ehip_ready EXPORT_OF alt_ehipc3_fm_0.o_ehip_ready
	set_interface_property o_rx_block_lock EXPORT_OF alt_ehipc3_fm_0.o_rx_block_lock
	set_interface_property o_rx_am_lock EXPORT_OF alt_ehipc3_fm_0.o_rx_am_lock
	set_interface_property o_rx_hi_ber EXPORT_OF alt_ehipc3_fm_0.o_rx_hi_ber
	set_interface_property o_local_fault_status EXPORT_OF alt_ehipc3_fm_0.o_local_fault_status
	set_interface_property o_remote_fault_status EXPORT_OF alt_ehipc3_fm_0.o_remote_fault_status
	set_interface_property i_clk_tx EXPORT_OF alt_ehipc3_fm_0.i_clk_tx
	set_interface_property i_clk_rx EXPORT_OF alt_ehipc3_fm_0.i_clk_rx
	set_interface_property i_csr_rst_n EXPORT_OF alt_ehipc3_fm_0.i_csr_rst_n
	set_interface_property i_tx_rst_n EXPORT_OF alt_ehipc3_fm_0.i_tx_rst_n
	set_interface_property i_rx_rst_n EXPORT_OF alt_ehipc3_fm_0.i_rx_rst_n
	set_interface_property tx_streaming EXPORT_OF alt_ehipc3_fm_0.tx_streaming
	set_interface_property rx_streaming EXPORT_OF alt_ehipc3_fm_0.rx_streaming
	set_interface_property nonpcs_ports EXPORT_OF alt_ehipc3_fm_0.nonpcs_ports
	set_interface_property pfc_ports EXPORT_OF alt_ehipc3_fm_0.pfc_ports
	set_interface_property pause_ports EXPORT_OF alt_ehipc3_fm_0.pause_ports
}

proc do_adjust_etile_eth_ip_4x25g {} {
	set_instance_parameter_value alt_ehipc3_fm_0 {ENABLE_RSFEC} {1}
	set_instance_parameter_value alt_ehipc3_fm_0 {core_variant} {1}
	set_instance_parameter_value alt_ehipc3_fm_0 {ehip_mode_gui_sl_0} {MAC+PCS+RSFEC}
	set_instance_parameter_value alt_ehipc3_fm_0 {link_fault_mode_gui_sl_0} {OFF}
	set_instance_parameter_value alt_ehipc3_fm_0 {number_of_channel} {3}
	set_instance_parameter_value alt_ehipc3_fm_0 {rx_max_frame_size_gui_sl_0} {16383}
	set_instance_parameter_value alt_ehipc3_fm_0 {rx_vlan_detection_gui_sl_0} {0}
	set_instance_parameter_value alt_ehipc3_fm_0 {tx_max_frame_size_gui_sl_0} {16383}
	set_instance_parameter_value alt_ehipc3_fm_0 {tx_vlan_detection_gui_sl_0} {0}

	set_interface_property rsfec_reconfig EXPORT_OF alt_ehipc3_fm_0.rsfec_reconfig
}

proc do_adjust_etile_eth_ip_4x10g {} {
	set_instance_parameter_value alt_ehipc3_fm_0 {core_variant} {1}
	set_instance_parameter_value alt_ehipc3_fm_0 {ehip_rate_gui_sl_0} {10G}
	set_instance_parameter_value alt_ehipc3_fm_0 {link_fault_mode_gui_sl_0} {OFF}
	set_instance_parameter_value alt_ehipc3_fm_0 {number_of_channel} {3}
	set_instance_parameter_value alt_ehipc3_fm_0 {rx_max_frame_size_gui_sl_0} {16383}
	set_instance_parameter_value alt_ehipc3_fm_0 {rx_vlan_detection_gui_sl_0} {0}
	set_instance_parameter_value alt_ehipc3_fm_0 {tx_max_frame_size_gui_sl_0} {16383}
	set_instance_parameter_value alt_ehipc3_fm_0 {tx_vlan_detection_gui_sl_0} {0}
}

# adjust parameters in "etile_eth_ip" system
proc do_adjust_etile_eth_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	# common IP core parameters
	set_instance_parameter_value alt_ehipc3_fm_0 {ENABLE_JTAG_AVMM} {1}

	# configuration-specific parameters
	$adjust_proc

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(ETH_PORT_SPEED,0) == 100} {
	set cb do_adjust_etile_eth_ip_1x100g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 25} {
	set cb do_adjust_etile_eth_ip_4x25g
} elseif {$PARAMS(ETH_PORT_SPEED,0) == 10} {
	set cb do_adjust_etile_eth_ip_4x10g
}

do_adjust_etile_eth_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
