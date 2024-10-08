package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# create the system "jtag_op_ip"
proc do_create_jtag_op_ip {device family ipname filename} {
	# create the system
	create_system $ipname
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance intel_jop_blaster_0 intel_jop_blaster
	set_instance_parameter_value intel_jop_blaster_0 {EXPORT_SLD_ED} {0}
	set_instance_parameter_value intel_jop_blaster_0 {MEM_SIZE} {4096}
	set_instance_parameter_value intel_jop_blaster_0 {MEM_WIDTH} {32}
	set_instance_parameter_value intel_jop_blaster_0 {USE_TCK_ENA} {0}
	set_instance_property intel_jop_blaster_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property clk EXPORT_OF intel_jop_blaster_0.clk
	set_interface_property reset EXPORT_OF intel_jop_blaster_0.reset
	set_interface_property avmm_s EXPORT_OF intel_jop_blaster_0.avmm_s

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="intel_jop_blaster_0">
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
do_create_jtag_op_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) [get_ip_filename $PARAMS(IP_COMP_NAME)]

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
