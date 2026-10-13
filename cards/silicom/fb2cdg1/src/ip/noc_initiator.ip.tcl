# noc_initiator.ip.tcl: TCL script for generating NOC initiator.
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)

proc do_adjust_noc_initiator_512 {} {
	set_instance_parameter_value intel_noc_initiator_0 {AXI4_DATA_MODE} {AXI4_DATA_MODE_512}

	set_interface_property noc_bridge_fabric_clk EXPORT_OF intel_noc_initiator_0.noc_bridge_fabric_clk
}

proc do_adjust_noc_initiator {device family ipname filename adjust_proc} {

    load_system $filename
    set_project_property DEVICE $device
    set_project_property DEVICE_FAMILY $family
    set_project_property HIDE_FROM_IP_CATALOG {true}

    set_instance_parameter_value intel_noc_initiator_0 {AXI4_DATA_MODE} {AXI4_DATA_MODE_256}
    set_instance_parameter_value intel_noc_initiator_0 {AXI4_HANDSHAKE} {AXI4_HANDSHAKE_STANDARD}
    set_instance_parameter_value intel_noc_initiator_0 {NUM_AXI4_IF} {16}

	$adjust_proc

    save_system $ipname
}
proc do_nothing {} {}

set cb do_nothing
if {$PARAMS(HBM_DATA_WIDTH) == 512} {
	set cb do_adjust_noc_initiator_512
}

do_adjust_noc_initiator $PARAMS(IP_DEVICE) $PARAMS(IP_DEVICE_FAMILY) $PARAMS(IP_COMP_NAME) $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)] $cb
