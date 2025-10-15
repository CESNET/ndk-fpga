package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

# adjust parameters in "hbm_ip" system (only bottom HBM specific)
proc do_adjust_hbm_ip_bottom {} {
	set_instance_parameter_value hbm_0 {PHY_HBM_LOCATION} {BOT}
	set_instance_parameter_value hbm_0 {PHY_DEFAULT_CORE_REF_CLK_FREQ} {0}
	set_instance_parameter_value hbm_0 {DIAG_RW_DATA_MONITOR} {1}
}

# adjust parameters in "hbm_ip" system (top)
proc do_adjust_hbm_ip {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value hbm_0 {PHY_BACKPRESSURE_LATENCY} {CYCLE_2}
	set_instance_parameter_value hbm_0 {PHY_CH1_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CH2_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CH3_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CH4_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CH5_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CH6_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CH7_EN} {1}
	set_instance_parameter_value hbm_0 {PHY_CORE_CLK_FREQ_MHZ} {200.0}
	set_instance_parameter_value hbm_0 {PHY_DEFAULT_REF_CLK_FREQ} {0}
	set_instance_parameter_value hbm_0 {PHY_HBM_LOCATION} {TOP}
	set_instance_parameter_value hbm_0 {PHY_HBM_USER_PLL_REF_CLK_IO_STD_ENUM} {LVDS_ONCHIP_TERMINATION}
	set_instance_parameter_value hbm_0 {PHY_MEM_CLK_FREQ_MHZ} {800.0}
	set_instance_parameter_value hbm_0 {PHY_USER_REF_CLK_FREQ_MHZ} {200.0}

	# configuration-specific parameters for bottom HBM only
	$adjust_proc

	set_interface_property mem_1 EXPORT_OF hbm_0.mem_1
	set_interface_property mem_2 EXPORT_OF hbm_0.mem_2
	set_interface_property mem_3 EXPORT_OF hbm_0.mem_3
	set_interface_property mem_4 EXPORT_OF hbm_0.mem_4
	set_interface_property mem_5 EXPORT_OF hbm_0.mem_5
	set_interface_property mem_6 EXPORT_OF hbm_0.mem_6
	set_interface_property mem_7 EXPORT_OF hbm_0.mem_7
	set_interface_property wmc_clk_1 EXPORT_OF hbm_0.wmc_clk_1
	set_interface_property phy_clk_1 EXPORT_OF hbm_0.phy_clk_1
	set_interface_property wmcrst_n_1 EXPORT_OF hbm_0.wmcrst_n_1
	set_interface_property axi_1_1 EXPORT_OF hbm_0.axi_1_1
	set_interface_property axi_1_0 EXPORT_OF hbm_0.axi_1_0
	set_interface_property axi_extra_1_1 EXPORT_OF hbm_0.axi_extra_1_1
	set_interface_property axi_extra_1_0 EXPORT_OF hbm_0.axi_extra_1_0
	set_interface_property apb_1 EXPORT_OF hbm_0.apb_1
	set_interface_property wmc_clk_2 EXPORT_OF hbm_0.wmc_clk_2
	set_interface_property wmc_clk_3 EXPORT_OF hbm_0.wmc_clk_3
	set_interface_property phy_clk_2 EXPORT_OF hbm_0.phy_clk_2
	set_interface_property phy_clk_3 EXPORT_OF hbm_0.phy_clk_3
	set_interface_property wmcrst_n_2 EXPORT_OF hbm_0.wmcrst_n_2
	set_interface_property wmcrst_n_3 EXPORT_OF hbm_0.wmcrst_n_3
	set_interface_property axi_2_1 EXPORT_OF hbm_0.axi_2_1
	set_interface_property axi_2_0 EXPORT_OF hbm_0.axi_2_0
	set_interface_property axi_3_1 EXPORT_OF hbm_0.axi_3_1
	set_interface_property axi_3_0 EXPORT_OF hbm_0.axi_3_0
	set_interface_property axi_extra_2_1 EXPORT_OF hbm_0.axi_extra_2_1
	set_interface_property axi_extra_2_0 EXPORT_OF hbm_0.axi_extra_2_0
	set_interface_property axi_extra_3_1 EXPORT_OF hbm_0.axi_extra_3_1
	set_interface_property axi_extra_3_0 EXPORT_OF hbm_0.axi_extra_3_0
	set_interface_property apb_2 EXPORT_OF hbm_0.apb_2
	set_interface_property apb_3 EXPORT_OF hbm_0.apb_3
	set_interface_property wmc_clk_4 EXPORT_OF hbm_0.wmc_clk_4
	set_interface_property wmc_clk_5 EXPORT_OF hbm_0.wmc_clk_5
	set_interface_property phy_clk_4 EXPORT_OF hbm_0.phy_clk_4
	set_interface_property phy_clk_5 EXPORT_OF hbm_0.phy_clk_5
	set_interface_property wmcrst_n_4 EXPORT_OF hbm_0.wmcrst_n_4
	set_interface_property wmcrst_n_5 EXPORT_OF hbm_0.wmcrst_n_5
	set_interface_property axi_4_1 EXPORT_OF hbm_0.axi_4_1
	set_interface_property axi_4_0 EXPORT_OF hbm_0.axi_4_0
	set_interface_property axi_5_1 EXPORT_OF hbm_0.axi_5_1
	set_interface_property axi_5_0 EXPORT_OF hbm_0.axi_5_0
	set_interface_property axi_extra_4_1 EXPORT_OF hbm_0.axi_extra_4_1
	set_interface_property axi_extra_4_0 EXPORT_OF hbm_0.axi_extra_4_0
	set_interface_property axi_extra_5_1 EXPORT_OF hbm_0.axi_extra_5_1
	set_interface_property axi_extra_5_0 EXPORT_OF hbm_0.axi_extra_5_0
	set_interface_property apb_4 EXPORT_OF hbm_0.apb_4
	set_interface_property apb_5 EXPORT_OF hbm_0.apb_5
	set_interface_property wmc_clk_6 EXPORT_OF hbm_0.wmc_clk_6
	set_interface_property wmc_clk_7 EXPORT_OF hbm_0.wmc_clk_7
	set_interface_property phy_clk_6 EXPORT_OF hbm_0.phy_clk_6
	set_interface_property phy_clk_7 EXPORT_OF hbm_0.phy_clk_7
	set_interface_property wmcrst_n_6 EXPORT_OF hbm_0.wmcrst_n_6
	set_interface_property wmcrst_n_7 EXPORT_OF hbm_0.wmcrst_n_7
	set_interface_property axi_6_1 EXPORT_OF hbm_0.axi_6_1
	set_interface_property axi_6_0 EXPORT_OF hbm_0.axi_6_0
	set_interface_property axi_7_1 EXPORT_OF hbm_0.axi_7_1
	set_interface_property axi_7_0 EXPORT_OF hbm_0.axi_7_0
	set_interface_property axi_extra_6_1 EXPORT_OF hbm_0.axi_extra_6_1
	set_interface_property axi_extra_6_0 EXPORT_OF hbm_0.axi_extra_6_0
	set_interface_property axi_extra_7_1 EXPORT_OF hbm_0.axi_extra_7_1
	set_interface_property axi_extra_7_0 EXPORT_OF hbm_0.axi_extra_7_0
	set_interface_property apb_6 EXPORT_OF hbm_0.apb_6
	set_interface_property apb_7 EXPORT_OF hbm_0.apb_7

	save_system $ipname
}

proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(IP_COMP_TYPE) == 0} {
    set cb do_nothing
} elseif {$PARAMS(IP_COMP_TYPE) == 1} {
    set cb do_adjust_hbm_ip_bottom
}

do_adjust_hbm_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
