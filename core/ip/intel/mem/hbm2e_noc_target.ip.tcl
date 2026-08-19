package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

# create the system "hbm2e_noc_target"
proc do_create_hbm2e_noc_target {device family ipname filename} {
	# create the system
	create_system $ipname
	set_project_property BOARD {}
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}
	set_use_testbench_naming_pattern 0 {}

	# add HDL parameters

	# add the components
	add_instance hbm_fp_0 hbm_fp
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_CLONE_OF_ID} {None}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PSEUDO_BL8_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_ADDR_ORDERING} {BGRBC}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_CLONE_OF_ID_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_CMD_USER_AP_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_HBM_DATA_MODE} {B256_DATA_MASK}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_PC0_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_PC0_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_PC0_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_PC1_POWER_EST_BANDWIDTH_PCT} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_PC1_POWER_EST_PAGE_HIT_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_PC1_POWER_EST_READ_PCT} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_POISON_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_POWER_DOWN_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_PSEUDO_BL8_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_RCMD_USER_AP_POLICY} {RDAP_HINT}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_REFRESH_MODE} {RFSH_MODE_CTRL_RFSH_ALL}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_TEMP010_THROTTLE_RATIO} {25}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_TEMP110_THROTTLE_RATIO} {50}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_TEMP_THROTTLE_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_WCMD_USER_AP_POLICY} {WRAP_HINT}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_AXI4LITE_MODE} {AXI4LITE_MODE_NONE}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_CORE_CLK_FREQ_MHZ} {350}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_CORE_REFCLK_FREQ_MHZ} {100}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_CORE_REFCLK_FREQ_MHZ_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_DEFAULT_TRAFFIC_PATTERN} {Sequential_Medium}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_FABRIC_NOC_DFD_FIFO_BYPASS} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_FABRIC_NOC_MODE} {FABRIC_NOC_MODE_NONE}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_GEN_SIM} {1}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_GEN_SYNTH} {1}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_HDL_FORMAT} {HDL_FORMAT_VERILOG}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_HDL_FORMAT_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_LOCATION_ASSIGNMENTS} {LOCATION_ASSIGNMENTS_NONE}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_BRIDGE_CLK_FREQ_MHZ} {550}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_PAIRING} {ONE_TO_ONE}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_PAIRING_INTERNAL} {NONE}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_READ_TRANSACTION_SIZE} {64}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_REFCLK_FREQ_MHZ} {100}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_REFCLK_FREQ_MHZ_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_SECURITY} {SECURITY_NONE}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_NOC_WRITE_TRANSACTION_SIZE} {64}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH0_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH0_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH1_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH1_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH2_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH2_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH3_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH3_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH4_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH4_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH5_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH5_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH6_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH6_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH7_PC0_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_CH7_PC1_EN} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_ENABLED} {0}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_PMON_INTERNAL_JAMB} {1}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_TE_ADDR_ALU_ARG_WIDTH} {16}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_TE_DATA_DQ_RATIO} {8}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_TE_NUM_DM_ALUS} {2}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_TE_NUM_DQ_ALUS} {2}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_USER_RO_CLK_FREQ_MHZ} {400}
	set_instance_parameter_value hbm_fp_0 {EX_DESIGN_USE_PD_NOC_FLOW} {1}
	set_instance_parameter_value hbm_fp_0 {PHY_CALIBRATION_STATUS_EN} {1}
	set_instance_parameter_value hbm_fp_0 {PHY_CTRL_CH_IRQ_O_EN} {1}
	set_instance_parameter_value hbm_fp_0 {PHY_HPS_BOOT_EN} {0}
	set_instance_parameter_value hbm_fp_0 {PHY_MEMCLK_FREQ_MHZ} {1400}
	set_instance_parameter_value hbm_fp_0 {PHY_REFCLK_FREQ_MHZ} {100}
	set_instance_parameter_value hbm_fp_0 {PHY_REFCLK_FREQ_MHZ_AUTO_BOOL} {1}
	set_instance_parameter_value hbm_fp_0 {PHY_RESET_TYPE} {HBM_RESET_WITH_CALIBRATION}
	set_instance_property hbm_fp_0 AUTO_EXPORT true

	# add wirelevel expressions

	# preserve ports for debug

	# add the exports
	set_interface_property ch0_u0_wmc_intr EXPORT_OF hbm_fp_0.ch0_u0_wmc_intr
	set_interface_property ch0_u1_wmc_intr EXPORT_OF hbm_fp_0.ch0_u1_wmc_intr
	set_interface_property ch1_u0_wmc_intr EXPORT_OF hbm_fp_0.ch1_u0_wmc_intr
	set_interface_property ch1_u1_wmc_intr EXPORT_OF hbm_fp_0.ch1_u1_wmc_intr
	set_interface_property ch2_u0_wmc_intr EXPORT_OF hbm_fp_0.ch2_u0_wmc_intr
	set_interface_property ch2_u1_wmc_intr EXPORT_OF hbm_fp_0.ch2_u1_wmc_intr
	set_interface_property ch3_u0_wmc_intr EXPORT_OF hbm_fp_0.ch3_u0_wmc_intr
	set_interface_property ch3_u1_wmc_intr EXPORT_OF hbm_fp_0.ch3_u1_wmc_intr
	set_interface_property ch4_u0_wmc_intr EXPORT_OF hbm_fp_0.ch4_u0_wmc_intr
	set_interface_property ch4_u1_wmc_intr EXPORT_OF hbm_fp_0.ch4_u1_wmc_intr
	set_interface_property ch5_u0_wmc_intr EXPORT_OF hbm_fp_0.ch5_u0_wmc_intr
	set_interface_property ch5_u1_wmc_intr EXPORT_OF hbm_fp_0.ch5_u1_wmc_intr
	set_interface_property ch6_u0_wmc_intr EXPORT_OF hbm_fp_0.ch6_u0_wmc_intr
	set_interface_property ch6_u1_wmc_intr EXPORT_OF hbm_fp_0.ch6_u1_wmc_intr
	set_interface_property ch7_u0_wmc_intr EXPORT_OF hbm_fp_0.ch7_u0_wmc_intr
	set_interface_property ch7_u1_wmc_intr EXPORT_OF hbm_fp_0.ch7_u1_wmc_intr
	set_interface_property fabric_clk EXPORT_OF hbm_fp_0.fabric_clk
	set_interface_property hbm_reset_n EXPORT_OF hbm_fp_0.hbm_reset_n
	set_interface_property hbm_reset_in_prog EXPORT_OF hbm_fp_0.hbm_reset_in_prog
	set_interface_property cattrip EXPORT_OF hbm_fp_0.cattrip
	set_interface_property cattrip_i EXPORT_OF hbm_fp_0.cattrip_i
	set_interface_property temp EXPORT_OF hbm_fp_0.temp
	set_interface_property temp_i EXPORT_OF hbm_fp_0.temp_i
	set_interface_property local_cal_success EXPORT_OF hbm_fp_0.local_cal_success
	set_interface_property local_cal_fail EXPORT_OF hbm_fp_0.local_cal_fail
	set_interface_property uibpll_refclk EXPORT_OF hbm_fp_0.uibpll_refclk
	set_interface_property t_ch0_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch0_u0_axi4noc
	set_interface_property t_ch0_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch0_u1_axi4noc
	set_interface_property t_ch1_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch1_u0_axi4noc
	set_interface_property t_ch1_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch1_u1_axi4noc
	set_interface_property t_ch2_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch2_u0_axi4noc
	set_interface_property t_ch2_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch2_u1_axi4noc
	set_interface_property t_ch3_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch3_u0_axi4noc
	set_interface_property t_ch3_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch3_u1_axi4noc
	set_interface_property t_ch4_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch4_u0_axi4noc
	set_interface_property t_ch4_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch4_u1_axi4noc
	set_interface_property t_ch5_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch5_u0_axi4noc
	set_interface_property t_ch5_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch5_u1_axi4noc
	set_interface_property t_ch6_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch6_u0_axi4noc
	set_interface_property t_ch6_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch6_u1_axi4noc
	set_interface_property t_ch7_u0_axi4noc EXPORT_OF hbm_fp_0.t_ch7_u0_axi4noc
	set_interface_property t_ch7_u1_axi4noc EXPORT_OF hbm_fp_0.t_ch7_u1_axi4noc
	set_interface_property t_ch0_ch1_sb_axi4noc EXPORT_OF hbm_fp_0.t_ch0_ch1_sb_axi4noc
	set_interface_property t_ch2_ch3_sb_axi4noc EXPORT_OF hbm_fp_0.t_ch2_ch3_sb_axi4noc
	set_interface_property t_ch4_ch5_sb_axi4noc EXPORT_OF hbm_fp_0.t_ch4_ch5_sb_axi4noc
	set_interface_property t_ch6_ch7_sb_axi4noc EXPORT_OF hbm_fp_0.t_ch6_ch7_sb_axi4noc

	# set values for exposed HDL parameters

	# set the the module properties
	set_module_property BONUS_DATA {<?xml version="1.0" encoding="UTF-8"?>
<bonusData>
 <element __value="hbm_fp_0">
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
do_create_hbm2e_noc_target $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) [get_ip_filename $PARAMS(IP_COMP_NAME)]

# set system info parameters on exported interface, from bottom up
do_set_exported_interface_sysinfo_parameters
