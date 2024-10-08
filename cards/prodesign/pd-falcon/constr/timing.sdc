# timing.sdc: Timing constraints
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Denis Kurka <xkurka05@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

set_false_path -from pcie_rstn_pin_perst

create_clock -period 156.25MHz -name REF156M_R9A1 [get_ports {REFCLK_R9A1}]
create_clock -period 156.25MHz -name REF156M_R9C1 [get_ports {REFCLK_R9C1}]
create_clock -period 100MHz -name UFPGA_CLK100  [get_ports {UFPGA_CLK100}]

set PCIE_CLK_0 [get_clocks cm_i|pcie_i|pcie_core_i|pcie_core_i|pcie_s10_hip_ast_0|altera_avst512_iopll|altera_ep_g3x16_avst512_io_pll_s10_outclk0]
set PLL_CLK_0 [get_clocks cm_i|clk_gen_i|iopll_i|iopll_0_outclk0]
set MI_CLK [get_clocks cm_i|clk_gen_i|iopll_i|iopll_0_outclk3]
set OSC_CLK [get_clocks ALTERA_INSERTED_INTOSC_FOR_TRS|divided_osc_clk]
set TCK_CLK [get_clocks altera_reserved_tck]
set EMIF0_CLK [get_clocks s10_emif_ip_ch0_i|emif_s10_0_core_cal_master_clk]
set EMIF1_CLK [get_clocks s10_emif_ip_ch1_i|emif_s10_0_core_cal_master_clk]

set PCIE_CLK [get_clocks cm_i|pcie_i|pcie_core_i|pcie_core_i|pcie_s10_hip_ast_0|altera_pcie_s10_hip_ast_pipen1b_inst|altera_pcie_s10_hip_ast_pllnphy_inst|g_phy_g3x16.phy_g3x16|phy_g3x16|xcvr_hip_native|ch0]
set EHIP100G_CORE0_CLK [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE1_CLK [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE2_CLK [get_clocks cm_i|network_mod_i|eth_core_g[2].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]
set EHIP100G_CORE3_CLK [get_clocks cm_i|network_mod_i|eth_core_g[3].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|alt_ehipc3_hard_inst|E100GX4_FEC.altera_xcvr_native_inst|xcvr_native_s10_etile_0_example_design_4ln_ptp|tx_clkout|ch0]


# Fix hold timing issues on EHIP
set_clock_groups -asynchronous -group $PCIE_CLK_0 -group $PCIE_CLK
set_clock_groups -asynchronous -group $PLL_CLK_0 -group $PCIE_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE0_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE1_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE2_CLK -group $OSC_CLK
set_clock_groups -asynchronous -group $MI_CLK -group $EHIP100G_CORE3_CLK -group $OSC_CLK

set_false_path -to cm_i|network_mod_i|eth_core_g[*].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|RST_CTRL_100G.alt_ehipc3_reset_controller_inst|rx_reset_synchronizers|resync_chains[0].synchronizer_nocut|din_s1
set_false_path -to cm_i|network_mod_i|eth_core_g[*].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|RST_CTRL_100G.alt_ehipc3_reset_controller_inst|tx_reset_synchronizers|resync_chains[0].synchronizer_nocut|din_s1
set_false_path -to cm_i|network_mod_i|eth_core_g[*].network_mod_core_i|eth_port_speed_sel_g.etile_eth_ip_i|alt_ehipc3_0|RST_CTRL_100G.alt_ehipc3_reset_controller_inst|ehip_rst_seqinst|rxpfa_synchronizers|resync_chains[0].synchronizer_nocut|din_s1

# Fix recovery timing issues on EMIF
set_clock_groups -asynchronous -group $TCK_CLK -group $EMIF0_CLK
set_clock_groups -asynchronous -group $TCK_CLK -group $EMIF1_CLK

