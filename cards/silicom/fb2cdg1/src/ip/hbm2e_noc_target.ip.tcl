# hbm2e_noc_target.ip.tcl: TCL script for generating HBM NOC target.
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

proc do_adjust_noc_target_enable_bl8 {} {
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PSEUDO_BL8_EN} {1}
}

proc do_adjust_noc_target {device family ipname filename adjust_proc} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_PSEUDO_BL8_EN} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH0_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH1_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH2_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH3_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH4_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH5_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH6_EN} {1}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_CLONE_OF_ID} {0}
	set_instance_parameter_value hbm_fp_0 {CTRL_CH7_EN} {1}
    set_instance_parameter_value hbm_fp_0 {PHY_MEMCLK_FREQ_MHZ} {1400}
	set_instance_parameter_value hbm_fp_0 {PHY_REFCLK_FREQ_MHZ} {100}
	set_instance_parameter_value hbm_fp_0 {PHY_RESET_TYPE} {HBM_RESET_WITH_CALIBRATION}

	$adjust_proc

	save_system $ipname
}

proc do_nothing {} {}
set cb do_nothing
if {$PARAMS(HBM_DATA_WIDTH) == 512} {
	set cb do_adjust_noc_target_enable_bl8
}

do_adjust_noc_target $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
