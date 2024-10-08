array set PARAMS $IP_PARAMS_L

set IP_COMP_NAME $PARAMS(IP_COMP_NAME)
if {[get_ips -quiet $IP_COMP_NAME] eq ""} {
    if {$PARAMS(IP_GEN_FILES) eq true} {
        create_ip -name gtwizard_ultrascale -vendor xilinx.com -library ip -module_name $IP_COMP_NAME -dir $PARAMS(IP_BUILD_DIR) -force
    } else {
        create_ip -name gtwizard_ultrascale -vendor xilinx.com -library ip -module_name $IP_COMP_NAME
    }
}

set IP [get_ips $IP_COMP_NAME]

if {$PARAMS(NET_MOD_ARCH) eq "40GE"} {
    set_property -dict [list \
        CONFIG.CHANNEL_ENABLE {X0Y27 X0Y26 X0Y25 X0Y24} \
        CONFIG.ENABLE_OPTIONAL_PORTS {loopback_in rxpcsreset_in rxpd_in rxpmareset_in rxpolarity_in txpcsreset_in txpd_in txpmareset_in txpolarity_in rxresetdone_out txresetdone_out} \
        CONFIG.FREERUN_FREQUENCY {156.25} \
        CONFIG.INCLUDE_CPLL_CAL {1} \
        CONFIG.INS_LOSS_NYQ {14} \
        CONFIG.INTERNAL_PRESET {XLAUI} \
        CONFIG.PRESET {GTY-XLAUI} \
        CONFIG.RX_CB_MAX_LEVEL {2} \
        CONFIG.RX_DATA_DECODING {64B66B_ASYNC} \
        CONFIG.RX_MASTER_CHANNEL {X0Y24} \
        CONFIG.RX_OUTCLK_SOURCE {RXPROGDIVCLK} \
        CONFIG.RX_PPM_OFFSET {200} \
        CONFIG.RX_REFCLK_FREQUENCY {161.1328125} \
        CONFIG.RX_USER_DATA_WIDTH {64} \
        CONFIG.SIM_CPLL_CAL_BYPASS {0} \
        CONFIG.TXPROGDIV_FREQ_VAL {312.5} \
        CONFIG.TX_DATA_ENCODING {64B66B_ASYNC} \
        CONFIG.TX_MASTER_CHANNEL {X0Y24} \
        CONFIG.TX_OUTCLK_SOURCE {TXPROGDIVCLK} \
        CONFIG.TX_REFCLK_FREQUENCY {161.1328125} \
        CONFIG.TX_USER_DATA_WIDTH {64} \
    ] $IP
} elseif {$PARAMS(NET_MOD_ARCH) eq "CESNET_LL10GE"} {
    set_property -dict [list \
        CONFIG.CHANNEL_ENABLE {X0Y39} \
        CONFIG.ENABLE_OPTIONAL_PORTS {loopback_in rxpolarity_in txpolarity_in} \
        CONFIG.FREERUN_FREQUENCY {250} \
        CONFIG.INTERNAL_PRESET {10GBASE-R} \
        CONFIG.LOCATE_COMMON {EXAMPLE_DESIGN} \
        CONFIG.LOCATE_RX_USER_CLOCKING {CORE} \
        CONFIG.LOCATE_TX_USER_CLOCKING {EXAMPLE_DESIGN} \
        CONFIG.PRESET {GTY-10GBASE-R} \
        CONFIG.RX_BUFFER_MODE {0} \
        CONFIG.RX_COMMA_SHOW_REALIGN_ENABLE {false} \
        CONFIG.RX_DATA_DECODING {RAW} \
        CONFIG.RX_OUTCLK_SOURCE {RXOUTCLKPMA} \
        CONFIG.RX_PPM_OFFSET {200} \
        CONFIG.RX_REFCLK_FREQUENCY {161.1328125} \
        CONFIG.RX_USER_DATA_WIDTH {32} \
        CONFIG.TX_BUFFER_MODE {0} \
        CONFIG.TX_DATA_ENCODING {RAW} \
        CONFIG.TX_OUTCLK_SOURCE {TXPROGDIVCLK} \
        CONFIG.TX_REFCLK_FREQUENCY {161.1328125} \
        CONFIG.TX_USER_DATA_WIDTH {32} \
    ] $IP
} elseif {$PARAMS(NET_MOD_ARCH) eq "CESNET_LL40GE"} {
    set_property -dict [list \
        CONFIG.CHANNEL_ENABLE {X0Y27 X0Y26 X0Y25 X0Y24} \
        CONFIG.ENABLE_OPTIONAL_PORTS {loopback_in rxpcsreset_in rxpd_in rxpmareset_in rxpolarity_in txpcsreset_in txpd_in txpmareset_in txpolarity_in rxresetdone_out txresetdone_out} \
        CONFIG.FREERUN_FREQUENCY {250} \
        CONFIG.INCLUDE_CPLL_CAL {0} \
        CONFIG.INS_LOSS_NYQ {14} \
        CONFIG.INTERNAL_PRESET {XLAUI} \
        CONFIG.LOCATE_RX_USER_CLOCKING {CORE} \
        CONFIG.LOCATE_TX_USER_CLOCKING {CORE} \
        CONFIG.PRESET {GTY-XLAUI} \
        CONFIG.RX_BUFFER_MODE {0} \
        CONFIG.RX_CB_MAX_LEVEL {2} \
        CONFIG.RX_DATA_DECODING {RAW} \
        CONFIG.RX_MASTER_CHANNEL {X0Y24} \
        CONFIG.RX_PPM_OFFSET {200} \
        CONFIG.RX_REFCLK_FREQUENCY {161.1328125} \
        CONFIG.RX_USER_DATA_WIDTH {32} \
        CONFIG.SIM_CPLL_CAL_BYPASS {0} \
        CONFIG.TX_BUFFER_MODE {0} \
        CONFIG.TX_DATA_ENCODING {RAW} \
        CONFIG.TX_MASTER_CHANNEL {X0Y24} \
        CONFIG.TX_OUTCLK_SOURCE {TXPROGDIVCLK} \
        CONFIG.TX_REFCLK_FREQUENCY {161.1328125} \
        CONFIG.TX_USER_DATA_WIDTH {32} \
    ] $IP
}
