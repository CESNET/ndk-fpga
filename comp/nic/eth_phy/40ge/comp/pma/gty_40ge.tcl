
set gty_40ge [create_ip -name gtwizard_ultrascale -vendor xilinx.com -library ip -version 1.7 -module_name gty_40ge]

## Following parameters can be added:
#
#  CONFIG.CHANNEL_ENABLE {X0Y0 X0Y1 X0Y2 X0Y3} \
#  CONFIG.RX_MASTER_CHANNEL {X0Y0} \
#  CONFIG.TX_MASTER_CHANNEL {X0Y0} \
#
#  Also modify RX/TX_REFCLK_FREQUENCY  and FREERUN_FREQUENCY when necessary

# User Parameters
set_property -dict [list \
  CONFIG.ENABLE_OPTIONAL_PORTS {loopback_in rxpcsreset_in rxpd_in rxpmareset_in rxpolarity_in txpcsreset_in txpd_in txpmareset_in txpolarity_in rxresetdone_out txresetdone_out} \
  CONFIG.FREERUN_FREQUENCY {156.25} \
  CONFIG.GT_TYPE {GTY} \
  CONFIG.INCLUDE_CPLL_CAL {1} \
  CONFIG.INS_LOSS_NYQ {14} \
  CONFIG.INTERNAL_PRESET {XLAUI} \
  CONFIG.PRESET {GTY-XLAUI} \
  CONFIG.RX_CB_MAX_LEVEL {2} \
  CONFIG.RX_DATA_DECODING {64B66B_ASYNC} \
  CONFIG.RX_OUTCLK_SOURCE {RXPROGDIVCLK} \
  CONFIG.RX_PPM_OFFSET {200} \
  CONFIG.RX_REFCLK_FREQUENCY {322.265625} \
  CONFIG.RX_USER_DATA_WIDTH {64} \
  CONFIG.SIM_CPLL_CAL_BYPASS {0} \
  CONFIG.TXPROGDIV_FREQ_VAL {312.5} \
  CONFIG.TX_DATA_ENCODING {64B66B_ASYNC} \
  CONFIG.TX_OUTCLK_SOURCE {TXPROGDIVCLK} \
  CONFIG.TX_REFCLK_FREQUENCY {322.265625} \
  CONFIG.TX_USER_DATA_WIDTH {64} \
] [get_ips gty_40ge]

# Runtime Parameters
set_property -dict {
  GENERATE_SYNTH_CHECKPOINT {1}
} $gty_40ge

# Generate the IP
generate_target {synthesis instantiation_template simulation} [get_ips gty_40ge]

synth_ip [get_ips gty_40ge]


