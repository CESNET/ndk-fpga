package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# create the system "dr_ctrl_ip"
proc do_create_dr_ctrl_ip {device family ipname filename} {
	# create the system
	create_system $ipname
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance dr_f_0 dr_f
	set_instance_parameter_value dr_f_0 {DEV_BOARD} {1}
	set_instance_parameter_value dr_f_0 {DR_DMEM_SIZE} {128}
	set_instance_parameter_value dr_f_0 {DR_ED_CPRIPHY} {0}
	set_instance_parameter_value dr_f_0 {DR_ED_DPHY} {0}
	set_instance_parameter_value dr_f_0 {DR_ED_ETH} {0}
	set_instance_parameter_value dr_f_0 {DR_ED_ETH_CPRI} {0}
	set_instance_parameter_value dr_f_0 {DR_ED_VARIANT} {-1}
	set_instance_parameter_value dr_f_0 {DR_NIOS_DEBUG_PORTS} {0}
	set_instance_parameter_value dr_f_0 {DR_NIOS_GUI} {Internal}
	set_instance_parameter_value dr_f_0 {DR_PROTOCOL} {0}
	set_instance_parameter_value dr_f_0 {DR_RECOVERY_ENABLED} {Yes}
	set_instance_parameter_value dr_f_0 {ENABLE_ECC} {0}
	set_instance_parameter_value dr_f_0 {ENABLE_IP_TIMING} {0}
	set_instance_parameter_value dr_f_0 {ENABLE_PTP_AIB7CLK} {1}
	set_instance_parameter_value dr_f_0 {GEN_SIM} {1}
	set_instance_parameter_value dr_f_0 {GEN_SYNTH} {1}
	set_instance_parameter_value dr_f_0 {HDL_FORMAT} {1}
	set_instance_parameter_value dr_f_0 {TEST_SIP} {0}
	set_instance_parameter_value dr_f_0 {USE_STATIC_VCS_SETUP} {0}
	set_instance_parameter_value dr_f_0 {dr_f_2xcpri_1} {1}
	set_instance_parameter_value dr_f_0 {dr_f_2xeth_17_ptp} {1}
	set_instance_parameter_value dr_f_0 {dr_f_4xeth_17} {1}
	set_instance_parameter_value dr_f_0 {dr_f_cpri_1} {1}
	set_instance_parameter_value dr_f_0 {dr_f_eth_12} {1}
	set_instance_parameter_value dr_f_0 {dr_f_eth_14} {1}
	set_instance_parameter_value dr_f_0 {dr_f_eth_14_startup} {1}
	set_instance_parameter_value dr_f_0 {dr_f_eth_15} {1}
	set_instance_parameter_value dr_f_0 {dr_f_eth_15_ptp} {0}
	set_instance_parameter_value dr_f_0 {dr_f_eth_15_startup} {0}
	set_instance_parameter_value dr_f_0 {dr_f_eth_17} {1}
	set_instance_parameter_value dr_f_0 {dr_f_eth_7} {1}
	set_instance_parameter_value dr_f_0 {dr_f_eth_9} {1}
	set_instance_parameter_value dr_f_0 {dr_f_pmadir_1} {1}
	set_instance_parameter_value dr_f_0 {dr_f_pmadir_2} {1}
	set_instance_parameter_value dr_f_0 {dr_f_pmadir_3} {1}
	set_instance_parameter_value dr_f_0 {include_gavmm} {0}
	set_instance_parameter_value dr_f_0 {syspll_rate_gui} {0}
	set_instance_property dr_f_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property i_csr_clk EXPORT_OF dr_f_0.i_csr_clk
	set_interface_property i_cpu_clk EXPORT_OF dr_f_0.i_cpu_clk
	set_interface_property i_rst_n EXPORT_OF dr_f_0.i_rst_n
	set_interface_property o_dr_curr_profile_id EXPORT_OF dr_f_0.o_dr_curr_profile_id
	set_interface_property o_dr_new_cfg_applied EXPORT_OF dr_f_0.o_dr_new_cfg_applied
	set_interface_property i_dr_new_cfg_applied_ack EXPORT_OF dr_f_0.i_dr_new_cfg_applied_ack
	set_interface_property o_dr_in_progress EXPORT_OF dr_f_0.o_dr_in_progress
	set_interface_property o_dr_error_status EXPORT_OF dr_f_0.o_dr_error_status
	set_interface_property host_reconfig_slave EXPORT_OF dr_f_0.host_reconfig_slave

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="dr_f_0">
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
do_create_dr_ctrl_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) [get_ip_filename $PARAMS(IP_COMP_NAME)]

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
