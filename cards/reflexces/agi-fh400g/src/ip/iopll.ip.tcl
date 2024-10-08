package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# adjust parameters in "iopll_ip" system
proc do_adjust_iopll_ip {device family ipname filename} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value iopll_0 {gui_divide_factor_c0} {1}
	set_instance_parameter_value iopll_0 {gui_divide_factor_c1} {3}
	set_instance_parameter_value iopll_0 {gui_divide_factor_c2} {4}
	set_instance_parameter_value iopll_0 {gui_fixed_vco_frequency_ps} {1666.667}
	set_instance_parameter_value iopll_0 {gui_multiply_factor} {12}
	set_instance_parameter_value iopll_0 {gui_number_of_clocks} {4}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency0} {400.0}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency1} {300.0}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency2} {200.0}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency_ps0} {2500.0}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency_ps1} {3333.333}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency_ps2} {5000.0}
	set_instance_parameter_value iopll_0 {gui_pll_bandwidth_preset} {High}
	set_instance_parameter_value iopll_0 {gui_pll_vco_freq_band_0} {pll_freq_clk0_disabled}
	set_instance_parameter_value iopll_0 {gui_pll_vco_freq_band_1} {pll_freq_clk1_disabled}
	set_instance_parameter_value iopll_0 {gui_vco_frequency} {1200.0}
        set_instance_parameter_value iopll_0 {hp_qsys_scripting_mode} {0}

	set_interface_property outclk1 EXPORT_OF iopll_0.outclk1
	set_interface_property outclk2 EXPORT_OF iopll_0.outclk2
	set_interface_property outclk3 EXPORT_OF iopll_0.outclk3

	save_system $ipname
}

do_adjust_iopll_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
