package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

# adjust parameters in "onboard_ddr4_s10_ip" system (only IP 1 specific)
proc do_adjust_onboard_ddr4_s10_ip_1 {} {
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_AC_TO_CK_SKEW_NS} {-0.005}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_DQS_TO_CK_SKEW_NS} {-0.799}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_IS_SKEW_WITHIN_AC_DESKEWED} {0}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_MAX_CK_DELAY_NS} {1.293}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_MAX_DQS_DELAY_NS} {0.645}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_SKEW_BETWEEN_DQS_NS} {0.302}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_ALERT_N_DQS_GROUP} {4}
}

# adjust parameters in "onboard_ddr4_s10_ip" system (IP 0)
proc do_adjust_onboard_ddr4_s10_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_DQS_TO_CK_SKEW_NS} {-0.986}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_IS_SKEW_WITHIN_AC_DESKEWED} {1}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_IS_SKEW_WITHIN_DQS_DESKEWED} {0}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_MAX_CK_DELAY_NS} {1.424}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_MAX_DQS_DELAY_NS} {0.568}
	set_instance_parameter_value emif_s10_0 {BOARD_DDR4_SKEW_BETWEEN_DQS_NS} {0.262}
	set_instance_parameter_value emif_s10_0 {CTRL_DDR4_ECC_EN} {1}
	set_instance_parameter_value emif_s10_0 {DIAG_DDR4_ABSTRACT_PHY} {1}
	set_instance_parameter_value emif_s10_0 {DIAG_EXPORT_PLL_LOCKED} {1}
	set_instance_parameter_value emif_s10_0 {EX_DESIGN_GUI_DDR4_GEN_SYNTH} {0}
	set_instance_parameter_value emif_s10_0 {EX_DESIGN_GUI_DDR4_HDL_FORMAT} {HDL_FORMAT_VHDL}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_ALERT_N_DQS_GROUP} {8}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_ALERT_N_PLACEMENT_ENUM} {DDR4_ALERT_N_PLACEMENT_DATA_LANES}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_FORMAT_ENUM} {MEM_FORMAT_DISCRETE}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_ROW_ADDR_WIDTH} {17}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TCL} {19}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TDQSCK_PS} {175}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TDQSQ_UI} {0.17}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TIH_PS} {87}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TIS_PS} {62}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TQH_UI} {0.74}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TRCD_NS} {12.5}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TRFC_NS} {350.0}
	set_instance_parameter_value emif_s10_0 {MEM_DDR4_TRP_NS} {12.5}


	# configuration-specific parameters for bottom HBM only
	$adjust_proc

	set_interface_property pll_locked EXPORT_OF emif_s10_0.pll_locked
	set_interface_property ctrl_ecc_user_interrupt_0 EXPORT_OF emif_s10_0.ctrl_ecc_user_interrupt_0

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(IP_COMP_TYPE) == 0} {
    set cb do_nothing
} elseif {$PARAMS(IP_COMP_TYPE) == 1} {
    set cb do_adjust_onboard_ddr4_s10_ip_1
}

do_adjust_onboard_ddr4_s10_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
