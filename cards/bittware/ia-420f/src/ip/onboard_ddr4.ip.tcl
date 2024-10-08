package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(CORE_BASE)/src/ip/common.tcl

proc do_adjust_onboard_ddr4_ip_0 {} {
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_RTT_NOM_ENUM} {DDR4_RTT_NOM_ODT_DISABLED}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_RTT_PARK} {DDR4_RTT_PARK_RZQ_4}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_SPD_137_RCD_CA_DRV} {0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_SPD_138_RCD_CK_DRV} {64}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_AC_DEEMPHASIS_ENUM} {DEEMPHASIS_MODE_OFF}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_AC_IO_STD_ENUM} {IO_STD_SSTL_12}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_AC_MODE_ENUM} {OUT_OCT_40_CAL}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_CK_DEEMPHASIS_ENUM} {DEEMPHASIS_MODE_OFF}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_CK_IO_STD_ENUM} {IO_STD_SSTL_12}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_CK_MODE_ENUM} {OUT_OCT_40_CAL}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_DATA_IN_MODE_ENUM} {IN_OCT_60_CAL}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_DATA_IO_STD_ENUM} {IO_STD_POD_12}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_DATA_OUT_DEEMPHASIS_ENUM} {DEEMPHASIS_MODE_HIGH}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_DATA_OUT_MODE_ENUM} {OUT_OCT_40_CAL}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_PLL_REF_CLK_IO_STD_ENUM} {IO_STD_TRUE_DIFF_SIGNALING}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_RZQ_IO_STD_ENUM} {IO_STD_CMOS_12}
}

proc do_adjust_onboard_ddr4_ip_1 {} {
	set_instance_parameter_value emif_fm_0 {CTRL_DDR4_ECC_EN} {1}
	set_instance_parameter_value emif_fm_0 {CTRL_DDR4_ECC_READDATAERROR_EN} {1}
	set_instance_parameter_value emif_fm_0 {CTRL_DDR4_ECC_STATUS_EN} {1}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_MIMIC_HPS_EMIF} {1}

	set_interface_property ctrl_ecc_user_interrupt_0 EXPORT_OF emif_fm_0.ctrl_ecc_user_interrupt_0
	set_interface_property ctrl_ecc_readdataerror_0 EXPORT_OF emif_fm_0.ctrl_ecc_readdataerror_0
	set_interface_property ctrl_ecc_status EXPORT_OF emif_fm_0.ctrl_ecc_status
}

# adjust parameters in "onboard_ddr4_ip" system
proc do_adjust_onboard_ddr4_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	# common IP core parameters
	set_instance_parameter_value emif_fm_0 {DIAG_DDR4_EXPORT_SEQ_AVALON_SLAVE} {CAL_DEBUG_EXPORT_MODE_JTAG}
	set_instance_parameter_value emif_fm_0 {DIAG_DDR4_USE_TG_AVL_2} {1}
	set_instance_parameter_value emif_fm_0 {DIAG_DDRT_ENABLE_DEFAULT_MODE} {0}
	set_instance_parameter_value emif_fm_0 {DIAG_DDRT_ENABLE_USER_MODE} {1}
	set_instance_parameter_value emif_fm_0 {DIAG_EXPORT_PLL_LOCKED} {1}
	set_instance_parameter_value emif_fm_0 {DIAG_EXPORT_PLL_REF_CLK_OUT} {1}
	set_instance_parameter_value emif_fm_0 {EX_DESIGN_GUI_DDR4_GEN_SIM} {0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_ALERT_N_PLACEMENT_ENUM} {DDR4_ALERT_N_PLACEMENT_FM_LANE2}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_FORMAT_ENUM} {MEM_FORMAT_DISCRETE}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_ROW_ADDR_WIDTH} {16}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_SPEEDBIN_ENUM} {DDR4_SPEEDBIN_3200}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TCCD_L_CYC} {7}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TCL} {22}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TDIVW_TOTAL_UI} {0.23}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TDQSCK_PS} {160}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TDQSQ_UI} {0.2}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIH_DC_MV} {65}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIH_PS} {65}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIS_AC_MV} {90}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TIS_PS} {40}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TQH_UI} {0.7}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TQSH_CYC} {0.4}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRCD_NS} {13.75}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRFC_DLR_NS} {260.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRFC_NS} {350.0}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRP_NS} {13.75}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TRRD_L_CYC} {7}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TWTR_L_CYC} {10}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_TWTR_S_CYC} {4}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_VDIVW_TOTAL} {110}
	set_instance_parameter_value emif_fm_0 {MEM_DDR4_WTCL} {18}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_DEFAULT_REF_CLK_FREQ} {0}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_MEM_CLK_FREQ_MHZ} {1333.32}
	set_instance_parameter_value emif_fm_0 {PHY_DDR4_USER_REF_CLK_FREQ_MHZ} {33.333}

	# configuration-specific parameters
	$adjust_proc

	set_interface_property pll_ref_clk_out EXPORT_OF emif_fm_0.pll_ref_clk_out
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
