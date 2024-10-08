array set PARAMS $IP_PARAMS_L

set IP_COMP_NAME $PARAMS(IP_COMP_NAME)
if {[get_ips -quiet $IP_COMP_NAME] eq ""} {
    if {$PARAMS(IP_GEN_FILES) eq true} {
        create_ip -name xxv_ethernet -vendor xilinx.com -library ip -version 4.1 -module_name $IP_COMP_NAME -dir $PARAMS(IP_BUILD_DIR) -force
    } else {
        create_ip -name xxv_ethernet -vendor xilinx.com -library ip -version 4.1 -module_name $IP_COMP_NAME
    }
}

set IP [get_ips $IP_COMP_NAME]

set_property -dict [list \
  CONFIG.ADD_GT_CNTRL_STS_PORTS {1} \
  CONFIG.BASE_R_KR {BASE-R} \
  CONFIG.CORE {Ethernet PCS/PMA 64-bit} \
  CONFIG.ENABLE_PIPELINE_REG {1} \
  CONFIG.GT_GROUP_SELECT {Quad_X0Y3} \
  CONFIG.GT_REF_CLK_FREQ {161.1328125} \
  CONFIG.LINE_RATE {10} \
  CONFIG.NUM_OF_CORES {4} \
] $IP
