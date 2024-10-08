# timing.sdc: Timing constraints
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

derive_clock_uncertainty

#create_clock -name {clk_sys_100m_p} -period 10.000 -waveform {0 5} {clk_sys_100m_p}
#create_clock -name {clk_sys_bak_50m_p} -period 20.000 -waveform {0 10} {clk_sys_bak_50m_p}
create_clock -name {altera_reserved_tck} -period 41.667 [get_ports { altera_reserved_tck }]

#create_clock -name {refclk_fgt12ach0_p} -period 10.000 [get_ports refclk_fgt12ach0_p]
#create_clock -name {refclk_fgt12ach3_p} -period 6.510 [get_ports refclk_fgt12ach3_p]
create_clock -name {refclk_fgt12ach4_p} -period 6.4 [get_ports refclk_fgt12ach4_p]
#create_clock -name {refclk_fgt12ach5_p} -period 6.4 [get_ports refclk_fgt12ach5_p]
#create_clock -name {refclk_fgt12ach6_p} -period 5.425 [get_ports refclk_fgt12ach6_p]
create_clock -name {CLK_DDR4_CH2_P}     -period 30.0 [get_ports CLK_DDR4_CH2_P]

create_clock -name {refclk_pcie_14c_ch0_p} -period 10.000 -waveform {0 5} {refclk_pcie_14c_ch0_p}
create_clock -name {refclk_pcie_14c_ch1_p} -period 10.000 -waveform {0 5} {refclk_pcie_14c_ch1_p}
create_clock -name {refclk_cxl_15c_ch0_p} -period 10.000 -waveform {0 5} {refclk_cxl_15c_ch0_p}
create_clock -name {refclk_cxl_15c_ch1_p} -period 10.000 -waveform {0 5} {refclk_cxl_15c_ch1_p}

# Cut (set_false_path) this JTAG clock from all other clocks in the design
set_clock_groups -asynchronous -group [get_clocks altera_reserved_tck]

# ===========
# Global clks
# ===========
set MI_CLK_CH3  [get_clocks ag_i|clk_gen_i|iopll_i|iopll_0_outclk3]


# ===========
# 10G8 design
# ===========
set FHIP_10G8_CLK_CH16 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[7].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch16]
set FHIP_10G8_CLK_CH18 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[5].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch18]
set FHIP_10G8_CLK_CH17 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[6].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch17]
set FHIP_10G8_CLK_CH19 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[4].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch19]
set FHIP_10G8_CLK_CH22 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[1].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch22]
set FHIP_10G8_CLK_CH21 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[2].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch21]
set FHIP_10G8_CLK_CH20 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[3].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch20]
set FHIP_10G8_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x10g1_g.eth_ip_g[0].FTILE_8x10g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 10G8 design 
set_clock_groups -asynchronous -group $FHIP_10G8_CLK_CH23 -group $FHIP_10G8_CLK_CH16
set_clock_groups -asynchronous -group $FHIP_10G8_CLK_CH23 -group $FHIP_10G8_CLK_CH17
set_clock_groups -asynchronous -group $FHIP_10G8_CLK_CH23 -group $FHIP_10G8_CLK_CH21
set_clock_groups -asynchronous -group $FHIP_10G8_CLK_CH23 -group $FHIP_10G8_CLK_CH22
set_clock_groups -asynchronous -group $FHIP_10G8_CLK_CH23 -group $FHIP_10G8_CLK_CH18
set_clock_groups -asynchronous -group $FHIP_10G8_CLK_CH23 -group $FHIP_10G8_CLK_CH20
set_clock_groups -asynchronous -group $FHIP_10G8_CLK_CH23 -group $FHIP_10G8_CLK_CH19


# ===========
# 25G8 design
# ===========
set FHIP_25G8_CLK_CH16 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[7].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch16]
set FHIP_25G8_CLK_CH17 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[6].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch17]
set FHIP_25G8_CLK_CH21 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[2].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch21]
set FHIP_25G8_CLK_CH22 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[1].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch22]
set FHIP_25G8_CLK_CH18 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[5].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch18]
set FHIP_25G8_CLK_CH20 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[3].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch20]
set FHIP_25G8_CLK_CH19 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[4].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch19]
set FHIP_25G8_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x25g1_g.eth_ip_g[0].FTILE_8x25g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 40G2 design 
set_clock_groups -asynchronous -group $FHIP_25G8_CLK_CH23 -group $FHIP_25G8_CLK_CH16
set_clock_groups -asynchronous -group $FHIP_25G8_CLK_CH23 -group $FHIP_25G8_CLK_CH17
set_clock_groups -asynchronous -group $FHIP_25G8_CLK_CH23 -group $FHIP_25G8_CLK_CH21
set_clock_groups -asynchronous -group $FHIP_25G8_CLK_CH23 -group $FHIP_25G8_CLK_CH22
set_clock_groups -asynchronous -group $FHIP_25G8_CLK_CH23 -group $FHIP_25G8_CLK_CH18
set_clock_groups -asynchronous -group $FHIP_25G8_CLK_CH23 -group $FHIP_25G8_CLK_CH20
set_clock_groups -asynchronous -group $FHIP_25G8_CLK_CH23 -group $FHIP_25G8_CLK_CH19


# ===========
# 40G2 design
# ===========
set FHIP_40G2_CLK_CH19 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_2x40g4_g.eth_ip_g[1].FTILE_2x40g4_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch19]
set FHIP_40G2_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_2x40g4_g.eth_ip_g[0].FTILE_2x40g4_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 40G2 design 
set_clock_groups -asynchronous -group $FHIP_40G2_CLK_CH23 -group $FHIP_40G2_CLK_CH19
set_clock_groups -asynchronous -group $MI_CLK_CH3         -group $FHIP_40G2_CLK_CH19
set_clock_groups -asynchronous -group $MI_CLK_CH3         -group $FHIP_40G2_CLK_CH23


# ===========
# 50G8 design
# ===========
set FHIP_50G8_CLK_CH9  [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[7].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch9 ]
set FHIP_50G8_CLK_CH11 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[6].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch11]
set FHIP_50G8_CLK_CH13 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[5].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch13]
set FHIP_50G8_CLK_CH17 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[3].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch17]
set FHIP_50G8_CLK_CH19 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[2].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch19]
set FHIP_50G8_CLK_CH15 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[4].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch15]
set FHIP_50G8_CLK_CH21 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[1].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch21]
set FHIP_50G8_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_8x50g1_g.eth_ip_g[0].FTILE_8x50g1_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 50G8 design 
set_clock_groups -asynchronous -group $$FHIP_50G8_CLK_CH23 -group $FHIP_50G8_CLK_CH9
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH9
set_clock_groups -asynchronous -group $$FHIP_50G8_CLK_CH23 -group $FHIP_50G8_CLK_CH11
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH11
set_clock_groups -asynchronous -group $$FHIP_50G8_CLK_CH23 -group $FHIP_50G8_CLK_CH13
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH13
set_clock_groups -asynchronous -group $$FHIP_50G8_CLK_CH23 -group $FHIP_50G8_CLK_CH17
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH17
set_clock_groups -asynchronous -group $$FHIP_50G8_CLK_CH23 -group $FHIP_50G8_CLK_CH19
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH19
set_clock_groups -asynchronous -group $$FHIP_50G8_CLK_CH23 -group $FHIP_50G8_CLK_CH15
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH15
set_clock_groups -asynchronous -group $$FHIP_50G8_CLK_CH23 -group $FHIP_50G8_CLK_CH21
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH21
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_50G8_CLK_CH23


# ============
# 100G2 design
# ============
set FHIP_100G2_CLK_CH19 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_2x100g4_g.eth_ip_g[1].FTILE_2x100g4_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch19]
set FHIP_100G2_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_2x100g4_g.eth_ip_g[0].FTILE_2x100g4_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 100G2 design 
set_clock_groups -asynchronous -group $FHIP_100G2_CLK_CH23 -group $FHIP_100G2_CLK_CH19
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_100G2_CLK_CH19
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_100G2_CLK_CH23


# ============
# 100G4 design
# ============
set FHIP_100G4_CLK_CH11 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_4x100g2_g.eth_ip_g[3].FTILE_4x100g2_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch11]
set FHIP_100G4_CLK_CH19 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_4x100g2_g.eth_ip_g[1].FTILE_4x100g2_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch19]
set FHIP_100G4_CLK_CH15 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_4x100g2_g.eth_ip_g[2].FTILE_4x100g2_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch15]
set FHIP_100G4_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_4x100g2_g.eth_ip_g[0].FTILE_4x100g2_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 100G4 design 
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_100G4_CLK_CH11
set_clock_groups -asynchronous -group $FHIP_100G4_CLK_CH23 -group $FHIP_100G4_CLK_CH11
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_100G4_CLK_CH19
set_clock_groups -asynchronous -group $FHIP_100G4_CLK_CH23 -group $FHIP_100G4_CLK_CH19
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_100G4_CLK_CH15
set_clock_groups -asynchronous -group $FHIP_100G4_CLK_CH23 -group $FHIP_100G4_CLK_CH15
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_100G4_CLK_CH23



# ============
# 200G2 design
# ============
set FHIP_200G2_CLK_CH15 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_2x200g4_g.eth_ip_g[1].ftile_2x200g4_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch15]
set FHIP_200G2_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_2x200g4_g.eth_ip_g[0].ftile_2x200g4_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 200G2 design 
set_clock_groups -asynchronous -group $FHIP_200G2_CLK_CH23 -group $FHIP_200G2_CLK_CH15
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_200G2_CLK_CH15
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_200G2_CLK_CH23


# ============
# 400G1 design
# ============
set FHIP_400G1_CLK_CH23 [get_clocks ag_i|network_mod_i|eth_core_g[0].network_mod_core_i|eth_port_mode_sel_g.ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 400G1 design 
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_400G1_CLK_CH23