# pcie4_uscale_plus.ip.tcl: generation script for the PCIe IP
# Copyright 2025 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

array set PARAMS $IP_PARAMS_L

set IP_COMP_NAME $PARAMS(IP_COMP_NAME)
if {[get_ips -quiet $IP_COMP_NAME] eq ""} {
    if {$PARAMS(IP_GEN_FILES) eq true} {
        create_ip -name pcie4c_uscale_plus -vendor xilinx.com -library ip -module_name $IP_COMP_NAME -dir $PARAMS(IP_BUILD_DIR) -force
    } else {
        create_ip -name pcie4c_uscale_plus -vendor xilinx.com -library ip -module_name $IP_COMP_NAME -dir $PARAMS(IP_BUILD_DIR)
    }
}

# Figure out if the name of the instance of the IP contains the index on its last character
set name_parts [split $IP_COMP_NAME _]
set last_part [lindex $name_parts end]
if {[string is integer -strict $last_part]} {
    set endpoint_idx $last_part
} else {
    set endpoint_idx 0
}

puts "The index of an endpoint is $endpoint_idx"

set IP [get_ips $IP_COMP_NAME]

# ==============================================================================
# general settings for each card
# ==============================================================================

set VENDOR_ID {18ec}
set PF0_DEVICE_ID {c000}

# ==============================================================================
# common properties they should be the same for all cards
# ==============================================================================

set config_list [list \
    CONFIG.ext_pcie_cfg_space_enabled {true} \
    CONFIG.extended_tag_field {true} \
    CONFIG.plltype {QPLL1} \
    CONFIG.axisten_freq {250} \
    CONFIG.AXISTEN_IF_ENABLE_CLIENT_TAG {true} \
    CONFIG.pf0_dev_cap_max_payload {512_bytes} \
    CONFIG.PF0_Use_Class_Code_Lookup_Assistant {false} \
    CONFIG.PF0_CLASS_CODE {020000} \
    CONFIG.MSI_X_OPTIONS {None} \
    CONFIG.mode_selection {Advanced} \
    CONFIG.pf0_msix_enabled {false} \
    CONFIG.pf1_msi_enabled {false} \
    CONFIG.pf1_msix_enabled {false} \
    CONFIG.pf0_bar0_64bit {true} \
    CONFIG.pf0_bar0_prefetchable {false} \
    CONFIG.pf0_bar0_scale {Megabytes} \
    CONFIG.pf0_bar0_size {64} \
    CONFIG.pf0_bar2_64bit {true} \
    CONFIG.pf0_bar2_prefetchable {false} \
    CONFIG.pf0_bar2_enabled {true} \
    CONFIG.pf0_bar2_scale {Megabytes} \
    CONFIG.pf0_bar2_size {16} \
    CONFIG.pf0_rbar_cap_bar0 {0xffffffffffff} \
    CONFIG.pf0_dsn_enabled {true} \
    CONFIG.PF0_MSIX_CAP_PBA_BIR {BAR_1:0} \
    CONFIG.PF0_MSIX_CAP_TABLE_BIR {BAR_1:0} \
    CONFIG.type1_membase_memlimit_enable {Disabled} \
    CONFIG.type1_prefetchable_membase_memlimit {Disabled} \
    CONFIG.cfg_ctl_if {true} \
    CONFIG.cfg_fc_if {true} \
    CONFIG.cfg_mgmt_if {false} \
    CONFIG.cfg_pm_if {false} \
    CONFIG.cfg_tx_msg_if {false} \
    CONFIG.rcv_msg_if {false} \
    CONFIG.tx_fc_if {false} \
    CONFIG.pf0_msi_enabled {false} \
]

if {$PARAMS(PCIE_ENDPOINT_MODE) == 2} {
    # x8_low_latency properties
    lappend config_list \
        CONFIG.pcie_blk_locn {X1Y1} \
        CONFIG.PL_LINK_CAP_MAX_LINK_SPEED {8.0_GT/s} \
        CONFIG.PL_LINK_CAP_MAX_LINK_WIDTH {X8} \
        CONFIG.axisten_if_width {256_bit} \
        CONFIG.coreclk_freq {500}
} else {
    if {$PARAMS(PCIE_ENDPOINT_MODE) == 1} {
        if {$endpoint_idx == 0} {
            lappend config_list CONFIG.pcie_blk_locn {X1Y1}
        } else {
            lappend config_list CONFIG.pcie_blk_locn {X1Y0}
        }

        lappend config_list \
            CONFIG.PL_LINK_CAP_MAX_LINK_SPEED {16.0_GT/s} \
            CONFIG.PL_LINK_CAP_MAX_LINK_WIDTH {X8}
    } else {
        lappend config_list \
            CONFIG.pcie_blk_locn {X1Y1} \
            CONFIG.PL_LINK_CAP_MAX_LINK_SPEED {8.0_GT/s} \
            CONFIG.PL_LINK_CAP_MAX_LINK_WIDTH {X16}
    }

    # x16 properties
    lappend config_list \
        CONFIG.AXISTEN_IF_EXT_512_CQ_STRADDLE {false} \
        CONFIG.AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE {true} \
        CONFIG.AXISTEN_IF_EXT_512_RQ_STRADDLE {true} \
        CONFIG.axisten_if_width {512_bit}
}

# set PCIE IDs, must be in last set_property
lappend config_list \
    CONFIG.PF0_DEVICE_ID [subst $PF0_DEVICE_ID] \
    CONFIG.PF0_SUBSYSTEM_ID [subst $PF0_DEVICE_ID] \
    CONFIG.PF0_SUBSYSTEM_VENDOR_ID [subst $VENDOR_ID] \
    CONFIG.vendor_id [subst $VENDOR_ID]

set_property -dict $config_list $IP
