# noc_clk_ctrl.ip.tcl: TCL script for generatingintel_noc_clock_ctrl.
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

proc do_adjust_noc_clk_ctrl {device family ipname filename} {

    load_system $filename
    set_project_property DEVICE $device
    set_project_property DEVICE_FAMILY $family
    set_project_property HIDE_FROM_IP_CATALOG {true}

    set_instance_parameter_value intel_noc_clock_ctrl_0 {REFCLK_FREQ} {NOC_PLL_REFCLK_FREQ_100_MHZ}

    set_interface_property refclk EXPORT_OF intel_noc_clock_ctrl_0.refclk
    set_interface_property pll_lock_o EXPORT_OF intel_noc_clock_ctrl_0.pll_lock_o
    set_interface_property target_inst_0 EXPORT_OF intel_noc_clock_ctrl_0.target_inst_0

    save_system $ipname
}

do_adjust_noc_clk_ctrl $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
