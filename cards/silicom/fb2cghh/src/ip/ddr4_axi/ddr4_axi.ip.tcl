array set PARAMS $IP_PARAMS_L

set IP_COMP_NAME $PARAMS(IP_COMP_NAME)
if {[get_ips -quiet $IP_COMP_NAME] eq ""} {
    if {$PARAMS(IP_GEN_FILES) eq true} {
        create_ip -name ddr4 -vendor xilinx.com -library ip -module_name $IP_COMP_NAME -dir $PARAMS(IP_BUILD_DIR) -force
    } else {
        create_ip -name ddr4 -vendor xilinx.com -library ip -module_name $IP_COMP_NAME
    }
}

set IP [get_ips $IP_COMP_NAME]

set_property -dict [list \
    CONFIG.C0.BANK_GROUP_WIDTH {1} \
    CONFIG.C0.DDR4_AxiDataWidth {512} \
    CONFIG.C0.DDR4_AxiSelection {true} \
    CONFIG.C0.DDR4_CLKFBOUT_MULT {5} \
    CONFIG.C0.DDR4_CasLatency {22} \
    CONFIG.C0.DDR4_CustomParts [subst $PARAMS(IP_MODIFY_BASE)/fb2cghh_onboard_ddr4.csv] \
    CONFIG.C0.DDR4_DataMask {NO_DM_NO_DBI} \
    CONFIG.C0.DDR4_DataWidth {72} \
    CONFIG.C0.DDR4_Ecc {true} \
    CONFIG.C0.DDR4_InputClockPeriod {3750} \
    CONFIG.C0.DDR4_MemoryPart {sdk_DDR4_2666} \
    CONFIG.C0.DDR4_isCustom {true} \
] $IP
