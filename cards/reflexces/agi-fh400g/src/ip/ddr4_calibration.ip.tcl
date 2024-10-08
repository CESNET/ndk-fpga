package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

proc do_adjust_ddr4_calibration_ip_0 {} {
}

proc do_adjust_ddr4_calibration_ip_1 {} {
	set_instance_parameter_value emif_cal_0 {NUM_CALBUS_INTERFACE} {2}

	set_interface_property emif_calbus_1 EXPORT_OF emif_cal_0.emif_calbus_1
}

# adjust parameters in "ddr4_calibration_ip" system
proc do_adjust_ddr4_calibration_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value emif_cal_0 {DIAG_EXPORT_SEQ_AVALON_SLAVE} {CAL_DEBUG_EXPORT_MODE_JTAG}

	# configuration-specific parameters
	$adjust_proc

	set_interface_property cal_debug_clk EXPORT_OF emif_cal_0.cal_debug_clk
	set_interface_property cal_debug_reset_n EXPORT_OF emif_cal_0.cal_debug_reset_n

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(IP_COMP_TYPE) == 0} {
	set cb do_adjust_ddr4_calibration_ip_0
} elseif {$PARAMS(IP_COMP_TYPE) == 1} {
	set cb do_adjust_ddr4_calibration_ip_1
}

do_adjust_ddr4_calibration_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
