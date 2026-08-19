# noc_pll.ip.tcl: TCL script for generating PLL.
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause
package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

# adjust parameters in "iopll_ip" system
proc do_adjust_noc_pll_ip {device family ipname filename} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

    set_instance_parameter_value iopll_0 {gui_number_of_clocks} {2}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency0} {400.0}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency1} {400.0}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency_ps0} {2500.0}
	set_instance_parameter_value iopll_0 {gui_output_clock_frequency_ps1} {2500.0}
	set_instance_parameter_value iopll_0 {gui_pll_bandwidth_preset} {High}
	set_instance_parameter_value iopll_0 {gui_pll_vco_freq_band_0} {pll_freq_clk0_band18}
	set_instance_parameter_value iopll_0 {gui_pll_vco_freq_band_1} {pll_freq_clk1_band18}
	set_instance_parameter_value iopll_0 {gui_vco_frequency} {600.0}
	set_instance_parameter_value iopll_0 {hp_qsys_scripting_mode} {0}

	set_interface_property outclk0 EXPORT_OF iopll_0.outclk0
	set_interface_property outclk1 EXPORT_OF iopll_0.outclk1

	save_system $ipname
}

do_adjust_noc_pll_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
