array set PARAMS $IP_PARAMS_L

set IP_COMP_NAME $PARAMS(IP_COMP_NAME)
if {[get_ips -quiet $IP_COMP_NAME] eq ""} {
    if {$PARAMS(IP_GEN_FILES) eq true} {
        create_ip -name pcie4_uscale_plus -vendor xilinx.com -library ip -module_name $IP_COMP_NAME -dir $PARAMS(IP_BUILD_DIR) -force
    } else {
        create_ip -name pcie4_uscale_plus -vendor xilinx.com -library ip -module_name $IP_COMP_NAME
    }
}

set IP [get_ips $IP_COMP_NAME]

# ==============================================================================
# general settings for each card
# ==============================================================================

set VENDOR_ID {1c2c}
set PF0_DEVICE_ID {00d2}

# specialties for the selected card


# ==============================================================================
# common properties they should be the same for all cards
# ==============================================================================

set config_list [list \
    CONFIG.PL_LINK_CAP_MAX_LINK_SPEED {8.0_GT/s} \
    CONFIG.ext_pcie_cfg_space_enabled {true} \
    CONFIG.extended_tag_field {true} \
    CONFIG.plltype {QPLL1} \
    CONFIG.axisten_freq {250} \
    CONFIG.AXISTEN_IF_ENABLE_CLIENT_TAG {true} \
    CONFIG.pf0_dev_cap_max_payload {512_bytes} \
    CONFIG.PF0_Use_Class_Code_Lookup_Assistant {false} \
    CONFIG.PF0_CLASS_CODE {020000} \
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
    CONFIG.pf0_msi_enabled {false} \
    CONFIG.pf0_msix_enabled {true} \
    CONFIG.PF0_MSIX_CAP_PBA_BIR {BAR_1:0} \
    CONFIG.PF0_MSIX_CAP_TABLE_BIR {BAR_1:0} \
    CONFIG.MSI_X_OPTIONS {MSI-X_External} \
    CONFIG.mode_selection {Advanced} \
    CONFIG.type1_membase_memlimit_enable {Disabled} \
    CONFIG.type1_prefetchable_membase_memlimit {Disabled} \
]

if {$PARAMS(PCIE_ENDPOINT_MODE) == 2} {
    # x8_low_latency properties
    lappend config_list \
        CONFIG.axisten_if_width {256_bit} \
        CONFIG.PL_LINK_CAP_MAX_LINK_WIDTH {X8} \
        CONFIG.coreclk_freq {500}
} else {
    # x16 properties
    lappend config_list \
        CONFIG.AXISTEN_IF_EXT_512_CQ_STRADDLE {false} \
        CONFIG.AXISTEN_IF_EXT_512_RC_4TLP_STRADDLE {true} \
        CONFIG.AXISTEN_IF_EXT_512_RQ_STRADDLE {true} \
        CONFIG.axisten_if_width {512_bit} \
        CONFIG.PL_LINK_CAP_MAX_LINK_WIDTH {X16}
}

# set PCIE IDs, must be in last set_property
lappend config_list \
    CONFIG.PF0_DEVICE_ID [subst $PF0_DEVICE_ID] \
    CONFIG.PF0_SUBSYSTEM_ID [subst $PF0_DEVICE_ID] \
    CONFIG.PF0_SUBSYSTEM_VENDOR_ID [subst $VENDOR_ID] \
    CONFIG.vendor_id [subst $VENDOR_ID]

set_property -dict $config_list $IP
