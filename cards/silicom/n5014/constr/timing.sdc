# timing.sdc: Timing constraints
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Martin Matějka <xmatej55@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

#create_clock -period 40.0 -name {altera_reserved_tck} [get_ports {altera_reserved_tck}]
create_clock -period 10.0 -name {clk_sys_100m}        [get_ports {SYS_CLK_100M}]
#create_clock -period 40.0 -name {spi_egress_sclk}     [get_ports {SPI_EGRESS_SCLK}]
create_clock -period 10.0 -name {clk_pcie_refclk0}    [get_ports {PCIE_REFCLK0}]
create_clock -period 10.0 -name {clk_pcie_refclk1}    [get_ports {PCIE_REFCLK1}]
create_clock -period 3.3333 -name {ddr4_ch0_ref_clk}  [get_ports {DDR4_CH0_REF_CLK}]
create_clock -period 3.3333 -name {ddr4_ch1_ref_clk}  [get_ports {DDR4_CH1_REF_CLK}]
create_clock -period 5.0 -name {hbm_top_ref_clk}      [get_ports {HBM_TOP_REF_CLK}]
create_clock -period 5.0 -name {hbm_bottom_ref_clk}   [get_ports {HBM_BOTTOM_REF_CLK}]

# ==============================================================================

set MI_CLK [get_clocks cm_i|clk_gen_i|iopll_i|iopll_0_outclk3]
set OSC_CLK [get_clocks ALTERA_INSERTED_INTOSC_FOR_TRS|divided_osc_clk]
set TCK_CLK [get_clocks altera_reserved_tck]

set EHIP100G_CORE0_CLK [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE1_CLK [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE2_CLK [get_clocks cm_i|network_mod_i|eth_core_g[2].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE3_CLK [get_clocks cm_i|network_mod_i|eth_core_g[3].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]

# Fix hold timing issues on EHIP
set_clock_groups -asynchronous -group $MI_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE0_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE1_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE2_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE3_CLK -group $OSC_CLK


# Create generated clock at sclk port derived from SCLK_reg pin
create_generated_clock \
 -source [get_pins {boot_i|spi_bridge_top_ss_i|spi_bridge_top|spi_bridge|spi_0|spi_0|SCLK_reg|clk}] \
 -divide_by 8 -multiply_by 1 -duty_cycle 50 -phase 0 -offset 0 \
 -name spi_sclk_internal [get_pins {boot_i|spi_bridge_top_ss_i|spi_bridge_top|spi_bridge|spi_0|spi_0|SCLK_reg|q}]

create_generated_clock \
 -source [get_pins {boot_i|spi_bridge_top_ss_i|spi_bridge_top|spi_bridge|spi_0|spi_0|SCLK_reg|q}] \
 -name spi_sclk [get_ports {SPI_SCLK}]

# Set multicycle constraints for setup
# clk2x/spi_sclk/2 = 100 MHz/12.5 MHz/2 = 4
set_multicycle_path 4 -setup -start -from [get_clocks {cm_i|clk_gen_i|iopll_i|iopll_0_outclk3}] -to spi_sclk
set_multicycle_path 4 -setup -end   -from spi_sclk -to [get_clocks {cm_i|clk_gen_i|iopll_i|iopll_0_outclk3}]

# Set multicycle constraints for setup
# clock_2x/spi_sclk - 1 = 100 MHz/12.5 MHz - 1 = 7
set_multicycle_path 7 -hold -start -from [get_clocks {cm_i|clk_gen_i|iopll_i|iopll_0_outclk3}] -to spi_sclk
set_multicycle_path 7 -hold -end   -from spi_sclk -to [get_clocks {cm_i|clk_gen_i|iopll_i|iopll_0_outclk3}]

# Set I/O delays
set_output_delay -clock spi_sclk -clock_fall -min  0 [get_ports {SPI_MOSI}]
set_output_delay -clock spi_sclk -clock_fall -max 15 [get_ports {SPI_MOSI}]

set_input_delay -clock spi_sclk -min  0 [get_ports {SPI_MISO}]
set_input_delay -clock spi_sclk -max 15 [get_ports {SPI_MISO}]

# False path for chip select.IP chip select is active at least 1 full clock cycle before clock is active.
set_false_path -to [get_ports {SPI_CS_L}]

# ==============================================================================
# Soft MAC constraints
# ==============================================================================

set_false_path -from [get_registers -nowarn {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|*|cdc_os_src_clk_toggle}] -to [get_registers -nowarn {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|*|v_gb.cdc_os_sync[0]}]
set_false_path -from [get_registers -nowarn {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|*|cdc_os_src_clk_toggle}] -to [get_registers -nowarn {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|*|cdc_os_sync[0]}]


set_false_path -from [get_registers -nowarn {*|v_gb.cdc_lf_sync[*][*]}]
set_false_path -to [get_registers -nowarn {*|v_gb.cdc_md_sync[0][*]*}]
set_false_path -to [get_registers *|xcvr_regfile|host_rdata[*]]

set_false_path -to [get_registers *|v_gb.cdc_lf_sync[0][0]]

set_false_path -from [get_registers -nowarn {*|pcs_100g_regfile|cgmii_lpbk_en}]
set_false_path -from [get_registers -nowarn {*|emac_core_regfile|*}]
set_false_path -to [get_registers -nowarn {*|emac_rmon_top|emac_gp_regfile|*}]
set_false_path -from [get_registers -nowarn {*|emac_top|avalon_mm_slave|host_addr[*]}]



#pkt clients. needed?
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth*_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth*_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|tx_keep[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|int_axi4_rx_tdata[*]}]
# avalon???
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_rx_top|emac_rx_userif|stavalon_rx_data[*]}]



set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|pcs_tx_en}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_clk_sync|pcs_tx_en_hclk_2_tx_xcvr_clk|v_gb.cdc_lf_sync[0][0]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|LPBK_SUPPORT.lpbk_eth_pcs_100g_generic_fifo_64w_bb_a|generic_fifo_base|rptr_gray[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|LPBK_SUPPORT.lpbk_eth_pcs_100g_generic_fifo_64w_bb_a|generic_fifo_base|rptr_gray_cdc_gb.rptr_gray_cdc_md_sync|v_gb.cdc_md_sync[*][*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|LPBK_SUPPORT.lpbk_eth_pcs_100g_generic_fifo_64w_bb_a|generic_fifo_base|rptr_gray[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|LPBK_SUPPORT.lpbk_eth_pcs_100g_generic_fifo_64w_bb_a|generic_fifo_base|rptr_gray_cdc_gb.rptr_gray_cdc_md_sync|v_gb.cdc_md_sync[*][*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|gen_xcvr_wrapper.xcvr_wrapper_top|xcvr_wrapper|ip_sel.xcvr_ip|xcvr_native_s10_etile_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|rx_reset_control_inst|g_rx.g_rx[*].g_rx.counter_rx_ready|r_reset}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|gen_xcvr_wrapper.xcvr_wrapper_top|xcvr_wrapper|ip_sel.rx_iopll_arst_n_lf_sync|v_gb.cdc_lf_sync[*][*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_rate_comp|eth_pcs_100g_rate_comp_fifo|generic_fifo_base|rptr_gray[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_rate_comp|eth_pcs_100g_rate_comp_fifo|generic_fifo_base|rptr_gray_cdc_gb.rptr_gray_cdc_md_sync|v_gb.cdc_md_sync[*][*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_rate_comp|ins_idles}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_rate_comp|sync_ins_idles|v_gb.cdc_lf_sync[*][*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_rate_comp|del_idles}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_rate_comp|sync_del_idles|v_gb.cdc_lf_sync[*][*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|lpbk_en}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|lpbk_en_reg[*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|LPBK_SUPPORT.lpbk_eth_pcs_100g_generic_fifo_64w_bb_a|generic_fifo_base|wptr_gray[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|LPBK_SUPPORT.lpbk_eth_pcs_100g_generic_fifo_64w_bb_a|generic_fifo_base|wptr_gray_cdc_gb.wptr_gray_cdc_md_sync|v_gb.cdc_md_sync[*][*]}]



set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|cgmii_lpbk_en}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|cgmii_tx*_mux[*][*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|int_axi4_rx_tkeep[*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|rem_bytes_neq_0}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_rx_top|emac_rx_userif|axi4_rx_tkeep[*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|rem_bytes_lt_min_rem_bytes}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|int_axi4_rx_terr}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_rx_top|emac_rx_fifo|dcfifo_520x128_bb|tmg_imprv_adapt_rd_lat_1.middle_dout[*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_rx_top|emac_rx_fifo|dcfifo_520x128_bb|tmg_imprv_adapt_rd_lat_1.dout[*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_rx_top|emac_rx_userif|rx_fifo_data_dl1[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|gen_pyld_length[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|wait_cnt[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_rx_top|emac_rx_userif|rx_fifo_rdata_r[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|axi4_rx_t*[*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|payload_count*[*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|tx_data[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|wait_cycles[1]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_gen|wait_cnt[*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_rx_top|emac_rx_fifo|dcfifo_520x128_bb|*}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|rec_intf_sel}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|int_axi4_rx_tuser[*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|gen_intf_sel}] \
   -to   [get_keepers -no_duplicates {GenCLVBBSReg[0].fim_pr_clv_if_reg|tx_pipeln|m_tdata_reg[*]}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client_regfile|pkt_mode}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|genblk_packet_client.eth_packet_client_wrapper|eth_packet_client|eth_packet_*|gen_pyld_length[*]}]


# Specify false path for tx_sel.tx_plls_tx_iopll_ip_0 LOCK output
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|gen_xcvr_wrapper.xcvr_wrapper_top|xcvr_wrapper|ip_sel.tx_plls.tx_iopll_ip_0|iopll_0|stratix10_altera_iopll_i|s10_iopll.fourteennm_pll~pll_e_reg__nff}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|gen_xcvr_wrapper.xcvr_wrapper_top|xcvr_wrapper|ip_sel.tx_plls.tx_iopll_reconfig_1_ip|*}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|gen_xcvr_wrapper.xcvr_wrapper_top|xcvr_wrapper|ip_sel.tx_plls.tx_iopll_ip_0|iopll_0|stratix10_altera_iopll_i|s10_iopll.fourteennm_pll~pll_e_reg__nff}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|gen_xcvr_wrapper.xcvr_wrapper_top|xcvr_wrapper|ip_sel.tx_plls.tx_iopll_ip_1|iopll_0|stratix10_altera_iopll_i|s10_iopll.fourteennm_pll~dprio_reg}]


set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|*|*}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|host_rdata[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_deskew_reorder_mla|*|*}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|*}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|*}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|host_rdata[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_ber_monitor|*}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|*}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|rst_i_sys_clk_resync|resync_chains[0].synchronizer_nocut|dreg[1]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth*_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|user_*x_sop_reg}]

# Relax timing in SMAC CSR module
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|inst_asynccsr_reset|resync_chains[*].synchronizer|dreg[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|[*].inst_mm_ctrl_*|avmm_state.AVMM_FSM_*}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|inst_synccsr_reset_2|resync_chains[*].synchronizer|dreg[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|[*].inst_mm_ctrl_*|avmm_state.AVMM_FSM_*}]
# set_false_path \
#    -from {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|inst_synccsr_reset_2|resync_chains[*].synchronizer|dreg[*]} \
#    -to   {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|[*].inst_mm_ctrl_*|inst_sync_rst_finish|resync_chains[*].synchronizer_nocut|din_s1}
# set_false_path \
#    -from {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|csr_reg[*][*]} \
#    -to   {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|[*].inst_mm_ctrl_*|inst_sync_*|resync_chains[*].synchronizer_nocut|din_s1}
# set_false_path \
#    -from {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|[*].inst_mm_ctrl_*|usr_*} \
#    -to   {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|[*].inst_mm_ctrl_*|inst_sync_*|resync_chains[*].synchronizer_nocut|din_s1}
# # RDJ removed. Causes CDC-50101. Maybe a local registered reset is better.
# #set_false_path -from [get_keepers -no_duplicates {reset_ctrl|rst_n_2x_int[*]}]                               -to [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|smac_hssi_csr_inst|*}]

## smac 2
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|cgmii_lpbk_en}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|cgmii_tx*_mux[*][*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|lpbk_en}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|lpbk_en_reg[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_am_lock|*}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|host_rdata[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_deskew_reorder_mla|bip8_checkers[*].eth_pcs_100g_rx_seq_bip8_checker|bip8_error[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|bip8_errcnt_vl[*][*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|rx_blksync_status_reg[*]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|host_rdata[*]}]

set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|rx_am_aligned_pipe|dly_bus[3][0]}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|host_rdata[*]}]
set_false_path \
   -from [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|eth_pcs_100g_core|eth_pcs_100g_rx_top|eth_pcs_100g_rx_ber_monitor|ber_status}] \
   -to   [get_keepers -no_duplicates {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_pcs_phy_wrapper.pcs_phy_wrapper|eth_pcs_100g_ip_top|eth_pcs_100g_top|REGFILE.eth_pcs_100g_regfile|ber_status_reg}]

set_max_skew \
    -get_skew_value_from_clock_period dst_clock_period \
    -skew_value_multiplier 0.8 \
    -from [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|wr_pkt_ptr_gray[*]}] \
    -to   [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|cdc_md_sync_wr_pkt_ptr_gray|v_gb.cdc_md_sync[0][*]}]
set_net_delay \
    -max \
    -get_value_from_clock_period dst_clock_period \
    -value_multiplier 0.8 \
    -from [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|wr_pkt_ptr_gray[*]}] \
    -to   [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth1_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|cdc_md_sync_wr_pkt_ptr_gray|v_gb.cdc_md_sync[0][*]}]

set_max_skew \
    -get_skew_value_from_clock_period dst_clock_period \
    -skew_value_multiplier 0.8 \
    -from [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|wr_pkt_ptr_gray[*]}] \
    -to   [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|cdc_md_sync_wr_pkt_ptr_gray|v_gb.cdc_md_sync[0][*]}]
set_net_delay \
    -max \
    -get_value_from_clock_period dst_clock_period \
    -value_multiplier 0.8 \
    -from [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|wr_pkt_ptr_gray[*]}] \
    -to   [get_registers {cm_i|clv_mod_i|mi32_eth_top_i|eth_top_i|eth_smac_wrapper|eth0_100g_wrapper|gen_inst_mac_rmon_wrapper.mac_rmon_wrapper|emac_top|emac_tx_top|emac_tx_fifo512|cdc_md_sync_wr_pkt_ptr_gray|v_gb.cdc_md_sync[0][*]}]

# Fix non-existing metastability issues
set_disable_timing -from * [get_cells {cm_i|clk_gen_i|reset_release_i|s10_user_rst_clkgate_0|lsm_gpo_out_user_reset}]
