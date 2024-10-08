package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# adjust parameters in "dr_ctrl_ip" system
proc do_adjust_dr_ctrl_ip {device family ipname filename} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value dr_f_0 {DR_ED_ETH} {1}
	set_instance_parameter_value dr_f_0 {DR_PROTOCOL} {1}
	set_instance_parameter_value dr_f_0 {HDL_FORMAT} {0}

	save_system $ipname
}

do_adjust_dr_ctrl_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
