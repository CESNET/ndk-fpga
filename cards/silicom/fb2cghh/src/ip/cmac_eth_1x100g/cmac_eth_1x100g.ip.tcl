array set PARAMS $IP_PARAMS_L

set IP_COMP_NAME $PARAMS(IP_COMP_NAME)
if {[get_ips -quiet $IP_COMP_NAME] eq ""} {
    if {$PARAMS(IP_GEN_FILES) eq true} {
        create_ip -name cmac_usplus -vendor xilinx.com -library ip -module_name $IP_COMP_NAME -dir $PARAMS(IP_BUILD_DIR) -force
    } else {
        create_ip -name cmac_usplus -vendor xilinx.com -library ip -module_name $IP_COMP_NAME
    }
}

set IP [get_ips $IP_COMP_NAME]

set_property -dict [list \
    CONFIG.ADD_GT_CNRL_STS_PORTS {1} \
    CONFIG.CMAC_CAUI4_MODE {1} \
    CONFIG.CMAC_CORE_SELECT {CMACE4_X0Y3} \
    CONFIG.GT_GROUP_SELECT {X0Y20~X0Y23} \
    CONFIG.GT_REF_CLK_FREQ {161.1328125} \
    CONFIG.INCLUDE_RS_FEC {1} \
    CONFIG.NUM_LANES {4x25} \
    CONFIG.RX_FLOW_CONTROL {0} \
    CONFIG.RX_MAX_PACKET_LEN {16383} \
    CONFIG.TX_FLOW_CONTROL {0} \
] $IP
