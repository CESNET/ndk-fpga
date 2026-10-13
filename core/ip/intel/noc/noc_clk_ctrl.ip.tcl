package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

# create the system "noc_clk_ctrl"
proc do_create_noc_clk_ctrl {device family ipname filename} {
	# create the system
	create_system $ipname
	set_project_property BOARD {}
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance intel_noc_clock_ctrl_0 intel_noc_clock_ctrl
	set_instance_parameter_value intel_noc_clock_ctrl_0 {REFCLK_FREQ} {NOC_PLL_REFCLK_FREQ_100_MHZ}
	set_instance_property intel_noc_clock_ctrl_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property refclk EXPORT_OF intel_noc_clock_ctrl_0.refclk
	set_interface_property pll_lock_o EXPORT_OF intel_noc_clock_ctrl_0.pll_lock_o
	set_interface_property target_inst_0 EXPORT_OF intel_noc_clock_ctrl_0.target_inst_0

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="intel_noc_clock_ctrl_0">
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
do_create_noc_clk_ctrl $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) [get_ip_filename $PARAMS(IP_COMP_NAME)]

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
