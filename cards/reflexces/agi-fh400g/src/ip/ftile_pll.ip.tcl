package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# adjust parameters in "ftile_pll_ip" system
proc do_adjust_ftile_pll_ip {device family ipname filename} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_0} {1}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_0} {ETHERNET_FREQ_830_156}

	set_interface_property out_refclk_fgt_0 EXPORT_OF systemclk_f_0.out_refclk_fgt_0

	save_system $ipname
}

do_adjust_ftile_pll_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
