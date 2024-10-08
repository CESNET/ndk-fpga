package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# adjust parameters in "ddr4_calibration_ip" system
proc do_adjust_ddr4_calibration_ip {device family ipname filename} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value emif_cal_0 {NUM_CALBUS_INTERFACE} {2}

	set_interface_property emif_calbus_1 EXPORT_OF emif_cal_0.emif_calbus_1

	save_system $ipname
}

do_adjust_ddr4_calibration_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
