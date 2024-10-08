package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# create the system "ftile_eth_ip"
proc do_create_ftile_eth_ip {device family ipname filename} {
	# create the system
	create_system $ipname
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance eth_f_0 eth_f
	set_instance_parameter_value eth_f_0 {ADV_MODE_GUI} {0}
	set_instance_parameter_value eth_f_0 {BCM_SIM_ENABLE} {0}
	set_instance_parameter_value eth_f_0 {BLOCK_TYPE_GUI} {0}
	set_instance_parameter_value eth_f_0 {CLIENT_INT_GUI} {0}
	set_instance_parameter_value eth_f_0 {CONT_MODE_TIMEOUT} {1}
	set_instance_parameter_value eth_f_0 {CUSTOM_CADENCE_GUI} {0}
	set_instance_parameter_value eth_f_0 {CUSTOM_RATE_GUI} {25.78125}
	set_instance_parameter_value eth_f_0 {CUSTOM_RXBIT_ROLLOVER} {0}
	set_instance_parameter_value eth_f_0 {DEV_BOARD} {1}
	set_instance_parameter_value eth_f_0 {DV_CWBIN_TIMEOUT} {0}
	set_instance_parameter_value eth_f_0 {DV_OVERRIDE} {0}
	set_instance_parameter_value eth_f_0 {ED_PACKET_GEN} {0}
	set_instance_parameter_value eth_f_0 {ED_PKTGEN_CONT_MODE} {0}
	set_instance_parameter_value eth_f_0 {ED_PKTGEN_LOOPCNT} {1}
	set_instance_parameter_value eth_f_0 {EHIP_RATE_GUI} {10G}
	set_instance_parameter_value eth_f_0 {ENABLE_ADME_GUI} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_ANLT_GUI} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_CWBIN_GUI} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_DL_GUI} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_DL_ML_GUI} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_ETK_GUI} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_PTP_AIB7CLK} {1}
	set_instance_parameter_value eth_f_0 {ENABLE_PTP_CHECK} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_PTP_DEBUG} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_RX_DIV33_CLK} {0}
	set_instance_parameter_value eth_f_0 {ENABLE_TX_DIV32_CLK} {0}
	set_instance_parameter_value eth_f_0 {EN_FHT_PRECODE_GUI} {0}
	set_instance_parameter_value eth_f_0 {ETH_MODE_GUI} {10G-1}
	set_instance_parameter_value eth_f_0 {ETH_VARIANT} {eth_7}
	set_instance_parameter_value eth_f_0 {EXAMPLE_DESIGN} {1}
	set_instance_parameter_value eth_f_0 {FAST_SIM_ENABLE} {1}
	set_instance_parameter_value eth_f_0 {FEC_MODE_25G_GUI} {0}
	set_instance_parameter_value eth_f_0 {GENERATE_SYSPLL} {0}
	set_instance_parameter_value eth_f_0 {GEN_BASE_PROFILE} {0}
	set_instance_parameter_value eth_f_0 {GEN_SEC_PROFILE} {0}
	set_instance_parameter_value eth_f_0 {GEN_SIM} {1}
	set_instance_parameter_value eth_f_0 {GEN_SYNTH} {1}
	set_instance_parameter_value eth_f_0 {HDL_FORMAT} {1}
	set_instance_parameter_value eth_f_0 {IP_TIMING} {0}
	set_instance_parameter_value eth_f_0 {LANE_NUM_GUI} {1}
	set_instance_parameter_value eth_f_0 {MODULATION_GUI} {0}
	set_instance_parameter_value eth_f_0 {NO_OF_PORTS} {1}
	set_instance_parameter_value eth_f_0 {NUM_100GE_PORT} {0}
	set_instance_parameter_value eth_f_0 {NUM_200GE_PORT} {0}
	set_instance_parameter_value eth_f_0 {NUM_25GE_PORT} {0}
	set_instance_parameter_value eth_f_0 {NUM_400GE_PORT} {0}
	set_instance_parameter_value eth_f_0 {NUM_50GE_PORT} {0}
	set_instance_parameter_value eth_f_0 {PACKING_EN_GUI} {0}
	set_instance_parameter_value eth_f_0 {PHY_REFCLK_GUI} {156.250000}
	set_instance_parameter_value eth_f_0 {PREAMBLE_PORTS} {1}
	set_instance_parameter_value eth_f_0 {PTP_MRIP_DEBUG} {0}
	set_instance_parameter_value eth_f_0 {RCFG_GRP} {25G-1}
	set_instance_parameter_value eth_f_0 {REFCLK_CWBIN_GUI} {100.0}
	set_instance_parameter_value eth_f_0 {RSFEC_TYPE_GUI} {0}
	set_instance_parameter_value eth_f_0 {SEC_PROFILE_NO} {0}
	set_instance_parameter_value eth_f_0 {SIP_TAG} {0}
	set_instance_parameter_value eth_f_0 {SRC_MANUAL} {2}
	set_instance_parameter_value eth_f_0 {SYSPLL_CUSTOM_GUI} {805.664062}
	set_instance_parameter_value eth_f_0 {SYSPLL_RATE_GUI} {0}
	set_instance_parameter_value eth_f_0 {TEST_SIP} {0}
	set_instance_parameter_value eth_f_0 {USE_CUSTOM_RXBIT_ROLLOVER} {0}
	set_instance_parameter_value eth_f_0 {XCVR_TYPE_GUI} {0}
	set_instance_parameter_value eth_f_0 {additional_ipg_removed_gui} {0}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_duplex_mode} {DUPLEX_MODE_FULL_DUPLEX}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_lpbk_mode} {LPBK_MODE_DISABLED}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_disable_link_fault_rf} {DISABLE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_flow_control_holdoff_mode} {MAC_PER_QUEUE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_force_link_fault_rf} {DISABLE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_pause_quanta} {65535}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_rxcrc_covers_preamble} {DISABLE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_tx_pause_daddr} {1652522221569}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_txcrc_covers_preamble} {DISABLE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_mac_use_am_insert} {DISABLE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_rx_en} {TRUE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_rx_pmadirect_single_width} {FALSE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_tx_en} {TRUE}
	set_instance_parameter_value eth_f_0 {bb_f_ehip_tx_pmadirect_single_width} {FALSE}
	set_instance_parameter_value eth_f_0 {enable_async_adapters_gui} {0}
	set_instance_parameter_value eth_f_0 {enable_cdr_clkout} {0}
	set_instance_parameter_value eth_f_0 {enable_ptp_gui} {0}
	set_instance_parameter_value eth_f_0 {enforce_max_frame_size_gui} {0}
	set_instance_parameter_value eth_f_0 {fgt_rx_pll_bw_sel} {LOW}
	set_instance_parameter_value eth_f_0 {fgt_rx_pll_l_cnt} {1}
	set_instance_parameter_value eth_f_0 {fgt_rx_pll_m_cnt} {1}
	set_instance_parameter_value eth_f_0 {fgt_rx_pll_manual_enable} {0}
	set_instance_parameter_value eth_f_0 {fgt_rx_pll_n_cnt} {1}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_bw_sel} {LOW}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_k_cnt} {0}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_l_cnt} {1}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_m_cnt} {165}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_manual_enable} {0}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_n_cnt} {4}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_refclk_freq_mhz} {156.250000}
	set_instance_parameter_value eth_f_0 {fgt_tx_pll_type} {FAST}
	set_instance_parameter_value eth_f_0 {flow_control_gui} {No}
	set_instance_parameter_value eth_f_0 {forward_rx_pause_requests_gui} {0}
	set_instance_parameter_value eth_f_0 {link_fault_mode_gui} {Off}
	set_instance_parameter_value eth_f_0 {preamble_passthrough_gui} {0}
	set_instance_parameter_value eth_f_0 {ptp_acc_mode_gui} {1}
	set_instance_parameter_value eth_f_0 {ptp_fp_width_gui} {8}
	set_instance_parameter_value eth_f_0 {ready_latency_gui} {0}
	set_instance_parameter_value eth_f_0 {rx_bytes_to_remove_gui} {Remove CRC bytes}
	set_instance_parameter_value eth_f_0 {rx_max_frame_size_gui} {1518}
	set_instance_parameter_value eth_f_0 {rx_vlan_detection_gui} {1}
	set_instance_parameter_value eth_f_0 {source_address_insertion_gui} {0}
	set_instance_parameter_value eth_f_0 {strict_preamble_checking_gui} {0}
	set_instance_parameter_value eth_f_0 {strict_sfd_checking_gui} {0}
	set_instance_parameter_value eth_f_0 {tx_ipg_size_gui} {12}
	set_instance_parameter_value eth_f_0 {tx_max_frame_size_gui} {1518}
	set_instance_parameter_value eth_f_0 {tx_vlan_detection_gui} {1}
	set_instance_parameter_value eth_f_0 {txmac_saddr_gui} {773588229205}
	set_instance_property eth_f_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property i_tx_clk EXPORT_OF eth_f_0.i_tx_clk
	set_interface_property i_rx_clk EXPORT_OF eth_f_0.i_rx_clk
	set_interface_property o_clk_pll EXPORT_OF eth_f_0.o_clk_pll
	set_interface_property i_reconfig_clk EXPORT_OF eth_f_0.i_reconfig_clk
	set_interface_property i_reconfig_reset EXPORT_OF eth_f_0.i_reconfig_reset
	set_interface_property o_sys_pll_locked EXPORT_OF eth_f_0.o_sys_pll_locked
	set_interface_property serial EXPORT_OF eth_f_0.serial
	set_interface_property i_clk_ref EXPORT_OF eth_f_0.i_clk_ref
	set_interface_property i_clk_sys EXPORT_OF eth_f_0.i_clk_sys
	set_interface_property reconfig_eth_slave EXPORT_OF eth_f_0.reconfig_eth_slave
	set_interface_property i_rst_n EXPORT_OF eth_f_0.i_rst_n
	set_interface_property i_tx_rst_n EXPORT_OF eth_f_0.i_tx_rst_n
	set_interface_property i_rx_rst_n EXPORT_OF eth_f_0.i_rx_rst_n
	set_interface_property reset_status_ports EXPORT_OF eth_f_0.reset_status_ports
	set_interface_property clock_status_ports EXPORT_OF eth_f_0.clock_status_ports
	set_interface_property clk_tx_div EXPORT_OF eth_f_0.clk_tx_div
	set_interface_property clk_rec_div64 EXPORT_OF eth_f_0.clk_rec_div64
	set_interface_property clk_rec_div EXPORT_OF eth_f_0.clk_rec_div
	set_interface_property status_ports EXPORT_OF eth_f_0.status_ports
	set_interface_property tx_mac_seg EXPORT_OF eth_f_0.tx_mac_seg
	set_interface_property rx_mac_seg EXPORT_OF eth_f_0.rx_mac_seg
	set_interface_property pfc_ports EXPORT_OF eth_f_0.pfc_ports
	set_interface_property sfc_ports EXPORT_OF eth_f_0.sfc_ports
	set_interface_property reconfig_xcvr_slave_0 EXPORT_OF eth_f_0.reconfig_xcvr_slave_0
	set_interface_property i_clk_pll EXPORT_OF eth_f_0.i_clk_pll

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="eth_f_0">
  <datum __value="_sortIndex" value="0" type="int" />
 </element>
</bonusData>
}
	set_module_property FILE {$filename}
	set_module_property GENERATION_ID {0x00000000}
	set_module_property NAME {$ipname}

	# save the system
	sync_sysinfo_parameters
	save_system $ipname
}

proc do_set_exported_interface_sysinfo_parameters {} {
}

# create all the systems, from bottom up
do_create_ftile_eth_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) [get_ip_filename $PARAMS(IP_COMP_NAME)]

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
