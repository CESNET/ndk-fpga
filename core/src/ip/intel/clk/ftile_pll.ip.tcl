package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# create the system "ftile_pll_ip"
proc do_create_ftile_pll_ip {device family ipname filename} {
	# create the system
	create_system $ipname
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance systemclk_f_0 systemclk_f
	set_instance_parameter_value systemclk_f_0 {cmnpll_dummy} {0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_refclk_src_0} {FHT RefClk #0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_refclk_src_1} {FHT RefClk #0}
	set_instance_parameter_value systemclk_f_0 {cmnpll_xtensa_src} {Auto}
	set_instance_parameter_value systemclk_f_0 {refclk_cdrclk_output_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_cdrclk_output_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_2} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_3} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_4} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_5} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_6} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_7} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_8} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_coreclk_enable_9} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_0} {156.250000}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_1} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_2} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_3} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_4} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_5} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_6} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_7} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_8} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_9} {NotSpecified}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_0} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_1} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_2} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_3} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_4} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_5} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_6} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_7} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_8} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_freq_mhz_txt_9} {100}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_0} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_1} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_2} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_3} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_4} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_5} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_6} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_7} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_8} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_9} {0}
	set_instance_parameter_value systemclk_f_0 {refclk_fht_freq_mhz_txt_0} {}
	set_instance_parameter_value systemclk_f_0 {refclk_fht_freq_mhz_txt_1} {}
	set_instance_parameter_value systemclk_f_0 {syspll_availpor_0} {1}
	set_instance_parameter_value systemclk_f_0 {syspll_availpor_1} {1}
	set_instance_parameter_value systemclk_f_0 {syspll_availpor_2} {1}
	set_instance_parameter_value systemclk_f_0 {syspll_flux_src} {Auto}
	set_instance_parameter_value systemclk_f_0 {syspll_freq_mhz_0} {805.6640625}
	set_instance_parameter_value systemclk_f_0 {syspll_freq_mhz_1} {805.6640625}
	set_instance_parameter_value systemclk_f_0 {syspll_freq_mhz_2} {805.6640625}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_0} {ETHERNET_FREQ_805_156}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_1} {Disabled}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_2} {Disabled}
	set_instance_parameter_value systemclk_f_0 {syspll_refclk_src_0} {RefClk #0}
	set_instance_parameter_value systemclk_f_0 {syspll_refclk_src_1} {RefClk #0}
	set_instance_parameter_value systemclk_f_0 {syspll_refclk_src_2} {RefClk #0}
	set_instance_property systemclk_f_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property out_systempll_synthlock_0 EXPORT_OF systemclk_f_0.out_systempll_synthlock_0
	set_interface_property out_systempll_clk_0 EXPORT_OF systemclk_f_0.out_systempll_clk_0
	set_interface_property refclk_fgt EXPORT_OF systemclk_f_0.refclk_fgt

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="systemclk_f_0">
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
do_create_ftile_pll_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) [get_ip_filename $PARAMS(IP_COMP_NAME)]

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
