package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

proc do_adjust_onboard_ddr4_ip_0 {board_rev} {
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_BANK_GROUP_WIDTH} {1}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_DQ_WIDTH} {64}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_FORMAT_ENUM} {MEM_FORMAT_DISCRETE}
	if {$board_rev == 0 || $board_rev == 1} {
		set_instance_parameter_value emif_fm_0 {MEM_DDR4_ROW_ADDR_WIDTH} {16}
	} elseif {$board_rev == 2} {
		set_instance_parameter_value emif_fm_0 {MEM_DDR4_ROW_ADDR_WIDTH} {17}
	}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_SPEEDBIN_ENUM} {DDR4_SPEEDBIN_2666}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TCCD_L_CYC} {7}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TCL} {21}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TFAW_NS} {30.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIH_PS} {80}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIS_PS} {55}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRCD_NS} {13.5}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRFC_DLR_NS} {350.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRFC_NS} {350.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRP_NS} {13.5}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRRD_L_CYC} {8}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRRD_S_CYC} {7}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TWTR_L_CYC} {10}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_WTCL} {14}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_MIMIC_HPS_EMIF} {1}
}

proc do_adjust_onboard_ddr4_ip_1 {board_rev} {
	set_instance_parameter_value emif_fm_0 {CTRL_DDR4_AUTO_PRECHARGE_EN} {1}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_AC_PARITY_LATENCY} {DDR4_AC_PARITY_LATENCY_4}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_ATCL_ENUM} {DDR4_ATCL_CL2}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_CK_WIDTH} {2}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_FINE_GRANULARITY_REFRESH} {DDR4_FINE_REFRESH_FIXED_2X}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_FORMAT_ENUM} {MEM_FORMAT_SODIMM}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_RANKS_PER_DIMM} {2}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_ROW_ADDR_WIDTH} {17}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_SPEEDBIN_ENUM} {DDR4_SPEEDBIN_3200}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TCCD_L_CYC} {8}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TCL} {26}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIH_PS} {65}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIS_PS} {40}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRCD_NS} {13.75}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRFC_DLR_NS} {260.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRP_NS} {13.75}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TWTR_L_CYC} {12}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_WTCL} {16}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_DEFAULT_REF_CLK_FREQ} {0}

	set_interface_property ctrl_auto_precharge_0 EXPORT_OF emif_fm_0.ctrl_auto_precharge_0
}

# adjust parameters in "onboard_ddr4_ip" system
proc do_adjust_onboard_ddr4_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	# common IP core parameters
	set_instance_parameter_value emif_fm_0 {DIAG_DDR4_EXPORT_SEQ_AVALON_SLAVE} {CAL_DEBUG_EXPORT_MODE_JTAG}
	set_instance_parameter_value emif_fm_0 {DIAG_EXPORT_PLL_LOCKED} {1}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TDQSCK_PS} {170}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TDQSQ_UI} {0.18}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIH_DC_MV} {65}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIS_AC_MV} {90}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TQH_UI} {0.74}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TQSH_CYC} {0.4}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TWTR_S_CYC} {4}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_MEM_CLK_FREQ_MHZ} {1333.33}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_REF_CLK_FREQ_MHZ} {33.333}

	# configuration-specific parameters
	if {$device == "AGIB027R29A1E2VR0"} {
		set board_rev 0
	} elseif {$device == "AGIB027R29A1E2VR3"} {
		set board_rev 1
	} elseif {$device == "AGIB027R29A1E2V"} {
		set board_rev 2
	} else {
		error "Incompatible FPGA device value: $device"
	}
	$adjust_proc $board_rev

	set_interface_property pll_locked EXPORT_OF emif_fm_0.pll_locked

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(IP_COMP_TYPE) == 0} {
	set cb do_adjust_onboard_ddr4_ip_0
} elseif {$PARAMS(IP_COMP_TYPE) == 1} {
	set cb do_adjust_onboard_ddr4_ip_1
}

do_adjust_onboard_ddr4_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
