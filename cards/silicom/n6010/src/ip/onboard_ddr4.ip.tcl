package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

# adjust parameters in "onboard_ddr4_ip" system
proc do_adjust_onboard_ddr4_ip {device family ipname filename} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value emif_fm_0 {DIAG_EXPORT_PLL_LOCKED} {1}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_ALERT_N_PLACEMENT_ENUM} {DDR4_ALERT_N_PLACEMENT_FM_LANE2}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_BANK_GROUP_WIDTH} {1}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_DM_EN} {0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_DQ_WIDTH} {32}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_FORMAT_ENUM} {MEM_FORMAT_DISCRETE}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_ROW_ADDR_WIDTH} {17}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TCL} {19}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TDQSCK_PS} {175}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TDQSQ_UI} {0.17}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TFAW_NS} {30.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIH_PS} {87}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIS_PS} {62}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TQH_UI} {0.74}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRCD_NS} {13.32}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRFC_DLR_NS} {190.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRFC_NS} {550.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRP_NS} {13.32}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRRD_L_CYC} {8}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRRD_S_CYC} {7}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_VDIVW_TOTAL} {130}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_DEFAULT_REF_CLK_FREQ} {0}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_CLAMSHELL_EN} {1}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_REF_CLK_FREQ_MHZ} {150.0}

	set_interface_property pll_locked EXPORT_OF emif_fm_0.pll_locked

	save_system $ipname
}

do_adjust_onboard_ddr4_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
