# ftile_pll.ip.tcl: TCL script for generating PLL.
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

# adjust parameters in "ftile_pll_ip" system
proc do_adjust_ftile_pll_ip {device family ipname filename} {

	load_system $filename
	set_project_property DEVICE $device
	set_project_property DEVICE_FAMILY $family
	set_project_property HIDE_FROM_IP_CATALOG {true}

	set_instance_parameter_value systemclk_f_0 {bk_cfg_kvcc_vreg_offset_en_val} {CFG_KVCC_VREG_OFFSET_EN_VAL_DISABLE}
	set_instance_parameter_value systemclk_f_0 {bk_ext_ac_cap} {EXTERNAL_AC_CAP_ENABLE}
	set_instance_parameter_value systemclk_f_0 {bk_rx_invert_p_and_n} {RX_INVERT_PN_DIS}
	set_instance_parameter_value systemclk_f_0 {bk_rx_termination} {RXTERM_OFFSET_P0}
	set_instance_parameter_value systemclk_f_0 {bk_tx_invert_p_and_n} {TX_INVERT_PN_DIS}
	set_instance_parameter_value systemclk_f_0 {bk_tx_termination} {TXTERM_OFFSET_P0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_main_tap} {41.5}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_1} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_2} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_3} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_post_tap_4} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_pre_tap_1} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_pre_tap_2} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txeq_pre_tap_3} {0.0}
	set_instance_parameter_value systemclk_f_0 {bk_txout_tristate_en} {TXOUT_TRISTATE_DIS}
	set_instance_parameter_value systemclk_f_0 {protocol_hard_pcie_lowloss} {DISABLE}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_0} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_1} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_2} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_3} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_4} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_5} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_6} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_7} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_8} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_always_active_9} {1}
	set_instance_parameter_value systemclk_f_0 {refclk_fgt_output_enable_0} {1}
	set_instance_parameter_value systemclk_f_0 {rx_ac_couple_enable} {ENABLE}
	set_instance_parameter_value systemclk_f_0 {rx_onchip_termination} {RX_ONCHIP_TERMINATION_R_2}
	set_instance_parameter_value systemclk_f_0 {rxeq_dfe_data_tap_1} {0}
	set_instance_parameter_value systemclk_f_0 {rxeq_hf_boost} {0}
	set_instance_parameter_value systemclk_f_0 {rxeq_vga_gain} {0}
	set_instance_parameter_value systemclk_f_0 {syspll_mod_0} {ETHERNET_FREQ_830_156}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_main_tap} {35}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_post_tap_1} {0}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_pre_tap_1} {5}
	set_instance_parameter_value systemclk_f_0 {ux_txeq_pre_tap_2} {0}
	set_instance_parameter_value systemclk_f_0 {vsr_mode} {VSR_MODE_DISABLE}

	set_interface_property out_refclk_fgt_0 EXPORT_OF systemclk_f_0.out_refclk_fgt_0

	save_system $ipname
}

do_adjust_ftile_pll_ip $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
