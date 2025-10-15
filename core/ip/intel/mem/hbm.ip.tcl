package require -exact qsys 24.1

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

# create the system "hbm_ip"
proc do_create_hbm_ip {device family ipname filename} {
	# create the system
	create_system $ipname
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance hbm_0 altera_hbm
	set_instance_parameter_value hbm_0 {CTRL_CH0_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH0_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH0_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH0_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH0_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {CTRL_CH1_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH1_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH1_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH1_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH1_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {CTRL_CH2_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH2_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH2_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH2_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH2_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {CTRL_CH3_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH3_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH3_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH3_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH3_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {CTRL_CH4_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH4_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH4_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH4_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH4_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {CTRL_CH5_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH5_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH5_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH5_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH5_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {CTRL_CH6_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH6_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH6_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH6_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH6_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {CTRL_CH7_AVMM_CMD_PRIOR_CTRL_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH7_AVMM_PRECHARGE_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH7_BL_ADVC_EN} {0}
	set_instance_parameter_value hbm_0 {CTRL_CH7_BL_ADVC_VAL} {3}
	set_instance_parameter_value hbm_0 {CTRL_CH7_CLONE_OF_ID_STR} {None}
	set_instance_parameter_value hbm_0 {DIAG_ABSTRACT_PHY} {1}
	set_instance_parameter_value hbm_0 {DIAG_EFFICIENCY_MONITOR} {0}
	set_instance_parameter_value hbm_0 {DIAG_ENABLE_JTAG_UART} {0}
	set_instance_parameter_value hbm_0 {DIAG_ENABLE_JTAG_UART_HEX} {0}
	set_instance_parameter_value hbm_0 {DIAG_ENABLE_PHY} {1}
	set_instance_parameter_value hbm_0 {DIAG_EXPORT_F2C_SLAVE} {0}
	set_instance_parameter_value hbm_0 {DIAG_EXPORT_UIBPLL_LOCKED} {0}
	set_instance_parameter_value hbm_0 {DIAG_EXTRA_CONFIGS} {}
	set_instance_parameter_value hbm_0 {DIAG_EX_DESIGN_ISSP_EN} {0}
	set_instance_parameter_value hbm_0 {DIAG_FAST_SIM_PLL} {1}
	set_instance_parameter_value hbm_0 {DIAG_FORCE_GENERATE_RW_IDS} {0}
	set_instance_parameter_value hbm_0 {DIAG_HBMC_TEST_MODE} {0}
	set_instance_parameter_value hbm_0 {DIAG_HBMC_TEST_PATTERN} {0}
	set_instance_parameter_value hbm_0 {DIAG_HBM_LFSR} {0}
	set_instance_parameter_value hbm_0 {DIAG_INFI_TG_ERR} {0}
	set_instance_parameter_value hbm_0 {DIAG_MEM_VERBOSE_DIS} {0}
	set_instance_parameter_value hbm_0 {DIAG_MIXED_TRAFFIC} {0}
	set_instance_parameter_value hbm_0 {DIAG_RD_PAR_DERR} {0}
	set_instance_parameter_value hbm_0 {DIAG_RUN_DEFAULT_PATTERN} {1}
	set_instance_parameter_value hbm_0 {DIAG_RUN_REPEAT_STAGE} {0}
	set_instance_parameter_value hbm_0 {DIAG_RUN_STRESS_STAGE} {0}
	set_instance_parameter_value hbm_0 {DIAG_RUN_USER_STAGE} {0}
	set_instance_parameter_value hbm_0 {DIAG_RW_DATA_MONITOR} {0}
	set_instance_parameter_value hbm_0 {DIAG_SBE_ECC} {0}
	set_instance_parameter_value hbm_0 {DIAG_SKIP_CAL} {1}
	set_instance_parameter_value hbm_0 {DIAG_TEST_RANDOM_AXI_READY} {0}
	set_instance_parameter_value hbm_0 {DIAG_TG_EFF_DATA_CHECK_EN} {1}
	set_instance_parameter_value hbm_0 {DIAG_TG_EXPORT_CFG_INTERFACE} {0}
	set_instance_parameter_value hbm_0 {DIAG_TG_READ_COUNT} {5000}
	set_instance_parameter_value hbm_0 {DIAG_TG_SEQUENCE} {TG_SEQUENCE_RANDOM}
	set_instance_parameter_value hbm_0 {DIAG_TG_WRITE_COUNT} {2500}
	set_instance_parameter_value hbm_0 {DIAG_TIMING_REGTEST_MODE} {0}
	set_instance_parameter_value hbm_0 {DIAG_WR_PAR_DERR} {0}
	set_instance_parameter_value hbm_0 {EX_DESIGN_GUI_GEN_SIM} {1}
	set_instance_parameter_value hbm_0 {EX_DESIGN_GUI_GEN_SYNTH} {1}
	set_instance_parameter_value hbm_0 {EX_DESIGN_GUI_HDL_FORMAT} {HDL_FORMAT_VERILOG}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH0_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH1_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH2_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH3_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH4_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH5_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH6_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_ADDR_ORDER} {BGRBC}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_HBMC_MODES_OVERRIDE} {PROD}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_HBMC_PC0_RL_OVERRIDE} {20}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_HBMC_PC0_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_HBMC_PC0_WL_OVERRIDE} {7}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_HBMC_PC1_SCR_EN_OVERRIDE} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_MECC_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_POWER_DOWN_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_TR_ORDER} {1}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_USER_DATA_WIDTH} {B256}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_USER_RD_AP_POL} {RDAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_USER_WR_AP_POL} {WRAP_HINT}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_CFG_WR_DM_EN} {0}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_RFSH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_0 {HARD_CTRL_CH7_RFSH_POLICY_OVERRIDE} {RFSH_POLICY_FLEXIBLE}
	set_instance_parameter_value hbm_0 {INTERNAL_TESTING_MODE} {0}
	set_instance_parameter_value hbm_0 {PHY_ADVANCED_PARAM_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_AXI_SWITCH_0_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_AXI_SWITCH_1_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_AXI_SWITCH_2_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_AXI_SWITCH_3_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_AXI_SWITCH_LOGICLOCK} {0}
	set_instance_parameter_value hbm_0 {PHY_BACKPRESSURE_LATENCY} {CYCLE_0}
	set_instance_parameter_value hbm_0 {PHY_C2P_RATE_ENUM} {RATE_HALF}
	set_instance_parameter_value hbm_0 {PHY_CH0_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CH1_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_CH2_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_CH3_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_CH4_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_CH5_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_CH6_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_CH7_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_CONFIG_ENUM} {CONFIG_PHY_AND_HARD_CTRL}
	set_instance_parameter_value hbm_0 {PHY_CORE_CLK_FREQ_MHZ} {250.0}
	set_instance_parameter_value hbm_0 {PHY_DEBOUNCE_PERIOD_MS} {20}
	set_instance_parameter_value hbm_0 {PHY_DEFAULT_CORE_REF_CLK_FREQ} {1}
	set_instance_parameter_value hbm_0 {PHY_DEFAULT_REF_CLK_FREQ} {1}
	set_instance_parameter_value hbm_0 {PHY_HBM_AXI_INTERFACE_0} {1}
	set_instance_parameter_value hbm_0 {PHY_HBM_AXI_INTERFACE_1} {1}
	set_instance_parameter_value hbm_0 {PHY_HBM_AXI_INTERFACE_2} {1}
	set_instance_parameter_value hbm_0 {PHY_HBM_AXI_INTERFACE_3} {1}
	set_instance_parameter_value hbm_0 {PHY_HBM_DEVICE_USER} {HBM_DEVICE_EMPTY}
	set_instance_parameter_value hbm_0 {PHY_HBM_LOCATION} {BOT}
	set_instance_parameter_value hbm_0 {PHY_HBM_USER_PLL_REF_CLK_IO_STD_ENUM} {LVDS_NO_ONCHIP_TERMINATION}
	set_instance_parameter_value hbm_0 {PHY_HBM_VENDOR_USER} {VENDOR_EMPTY}
	set_instance_parameter_value hbm_0 {PHY_MEM_CLK_FREQ_MHZ} {600.0}
	set_instance_parameter_value hbm_0 {PHY_PIPELINE_BRESP} {0}
	set_instance_parameter_value hbm_0 {PHY_PIPELINE_RRESP} {0}
	set_instance_parameter_value hbm_0 {PHY_PLACE_BACKPRESSURE_REGS} {1}
	set_instance_parameter_value hbm_0 {PHY_RATE_ENUM} {RATE_HALF}
	set_instance_parameter_value hbm_0 {PHY_RESET_DEBOUNCE_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_RX_PIPELINE_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_SW_0_MASTER_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_MASTER_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_MASTER_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_MASTER_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_MASTER_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_SLAVE_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_SLAVE_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_SLAVE_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_SLAVE_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_0_SLAVE_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_MASTER_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_MASTER_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_MASTER_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_MASTER_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_MASTER_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_SLAVE_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_SLAVE_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_SLAVE_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_SLAVE_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_1_SLAVE_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_MASTER_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_MASTER_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_MASTER_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_MASTER_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_MASTER_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_SLAVE_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_SLAVE_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_SLAVE_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_SLAVE_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_2_SLAVE_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_MASTER_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_MASTER_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_MASTER_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_MASTER_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_MASTER_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_SLAVE_0_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_SLAVE_1_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_SLAVE_2_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_SLAVE_3_SHARE_COUNT} {0}
	set_instance_parameter_value hbm_0 {PHY_SW_3_SLAVE_HONOR_REQ} {0}
	set_instance_parameter_value hbm_0 {PHY_TEMP_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_0 {PHY_TEMP_THROTTLE_THRESHOLD} {85}
	set_instance_parameter_value hbm_0 {PHY_THROTTLE_RDATA_BRESP} {1}
	set_instance_parameter_value hbm_0 {PHY_TX_PIPELINE_EN} {0}
	set_instance_parameter_value hbm_0 {PHY_USER_CORE_REF_CLK_FREQ_MHZ} {100.0}
	set_instance_parameter_value hbm_0 {PHY_USER_REF_CLK_FREQ_MHZ} {100.0}
	set_instance_parameter_value hbm_0 {PLL_ADD_EXTRA_CLKS} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_5} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_6} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_7} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_DUTY_CYCLE_GUI_8} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_5} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_6} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_7} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_FREQ_MHZ_GUI_8} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_5} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_6} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_7} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_DEG_GUI_8} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_5} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_6} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_7} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_ACTUAL_PHASE_PS_GUI_8} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_5} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_6} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_7} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_DUTY_CYCLE_GUI_8} {50.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_5} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_6} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_7} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_FREQ_MHZ_GUI_8} {100.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_PHASE_GUI_5} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_PHASE_GUI_6} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_PHASE_GUI_7} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_DESIRED_PHASE_GUI_8} {0.0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_0} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_1} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_2} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_3} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_4} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_5} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_6} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_7} {0}
	set_instance_parameter_value hbm_0 {PLL_EXTRA_CLK_PHASE_SHIFT_UNIT_GUI_8} {0}
	set_instance_parameter_value hbm_0 {PLL_USER_NUM_OF_EXTRA_CLKS} {0}
	set_instance_parameter_value hbm_0 {PROTOCOL_ENUM} {PROTOCOL_HBM}
	set_instance_parameter_value hbm_0 {TG_CFG_EN} {0}
	set_instance_parameter_value hbm_0 {TG_USE_EFFICIENCY_PATTERN} {0}
	set_instance_parameter_value hbm_0 {freshIP} {1}
	set_instance_property hbm_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property pll_ref_clk EXPORT_OF hbm_0.pll_ref_clk
	set_interface_property ext_core_clk EXPORT_OF hbm_0.ext_core_clk
	set_interface_property ext_core_clk_locked EXPORT_OF hbm_0.ext_core_clk_locked
	set_interface_property wmcrst_n_in EXPORT_OF hbm_0.wmcrst_n_in
	set_interface_property hbm_only_reset_in EXPORT_OF hbm_0.hbm_only_reset_in
	set_interface_property status EXPORT_OF hbm_0.status
	set_interface_property cal_lat EXPORT_OF hbm_0.cal_lat
	set_interface_property mem_0 EXPORT_OF hbm_0.mem_0
	set_interface_property m2u_bridge EXPORT_OF hbm_0.m2u_bridge
	set_interface_property wmc_clk_0 EXPORT_OF hbm_0.wmc_clk_0
	set_interface_property phy_clk_0 EXPORT_OF hbm_0.phy_clk_0
	set_interface_property wmcrst_n_0 EXPORT_OF hbm_0.wmcrst_n_0
	set_interface_property axi_0_0 EXPORT_OF hbm_0.axi_0_0
	set_interface_property axi_0_1 EXPORT_OF hbm_0.axi_0_1
	set_interface_property axi_extra_0_0 EXPORT_OF hbm_0.axi_extra_0_0
	set_interface_property axi_extra_0_1 EXPORT_OF hbm_0.axi_extra_0_1
	set_interface_property apb_0 EXPORT_OF hbm_0.apb_0

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="hbm_0">
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
do_create_hbm_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) [get_ip_filename $PARAMS(IP_COMP_NAME)]

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
