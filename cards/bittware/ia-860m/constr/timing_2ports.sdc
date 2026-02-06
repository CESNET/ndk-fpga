# timing.sdc: Timing constraints
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# Time Information
# ==============================================================================

set_time_format -unit ns -decimal_places 3

# ==============================================================================
# Create Clock
# ==============================================================================
# Main 100 MHz clock
create_clock -name {SYSCLK_100_P}            -period  10.000 [get_ports SYSCLK_100_P]
# R-Tile PCIe Ref Clocks 100MHz
create_clock -name {PCIE_REFCLK0}         -period  10.000 [get_ports PCIE_REFCLK0]
create_clock -name {PCIE_REFCLK1}         -period  10.000 [get_ports PCIE_REFCLK1]
# F-Tile Ref Clock Channel 5 156.25MHz - Refclk #5
create_clock -name {QSFP0_REFCLK}         -period   6.400 [get_ports QSFP0_REFCLK]
# F-Tile Ref Clock Channel 5 156.25MHz - Refclk #5
create_clock -name {QSFP1_REFCLK}         -period   6.400 [get_ports QSFP1_REFCLK]
# BMC Ingress SPI Clock 25MHz
create_clock -name {FPGA_IG_SPI_SCK}      -period  40.000 [get_ports FPGA_IG_SPI_SCK]

# 24MHz
create_clock -name {altera_reserved_tck} -period 24MHz {altera_reserved_tck}

# ===========
# Global clks
# ===========
set MI_CLK_CH3  [get_clocks cm_i|clk_gen_i|iopll_i|iopll_0_outclk3]
set SPI_CLK [get_clocks FPGA_IG_SPI_SCK]
set ALTERA_CLK [get_clocks altera_reserved_tck]

# ============
# 400G2 design
# ============
set FHIP_400G2_P0_CLK_CH23 [get_clocks cm_i|network_mod_i|eth_core_g[0].network_mod_core_i|ftile_1x400g8_g.eth_ip_g[0].ftile_1x400g8_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]
set FHIP_400G2_P1_CLK_CH23 [get_clocks cm_i|network_mod_i|eth_core_g[1].network_mod_core_i|ftile_1x400g8_g.eth_ip_g[0].ftile_1x400g8_i|ftile_eth_ip_i|eth_f_0|tx_clkout|ch23]

# Fix hold timing issues for 400G2 design
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_400G2_P0_CLK_CH23
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $FHIP_400G2_P1_CLK_CH23
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $SPI_CLK
set_clock_groups -asynchronous -group $MI_CLK_CH3          -group $ALTERA_CLK

# BMC SPI Ingress Timing
set_input_delay -clock FPGA_IG_SPI_SCK -max 8 -clock_fall [get_ports {FPGA_IG_SPI_MOSI}]
set_input_delay -clock FPGA_IG_SPI_SCK -min 2 -clock_fall [get_ports {FPGA_IG_SPI_MOSI}]
set_output_delay -clock FPGA_IG_SPI_SCK -max 22.5  [get_ports {FPGA_IG_SPI_MISO}]
set_output_delay -clock FPGA_IG_SPI_SCK -min 0     [get_ports {FPGA_IG_SPI_MISO}]
set_input_delay -clock SPI_CLK 2.5 [get_ports {FPGA_IG_SPI_SCK}]
set_input_delay -clock SPI_CLK 2.5 [get_ports {FPGA_IG_SPI_PCS0}]

# From "AV SoC Golden Hardware Reference Design"
set_input_delay -clock ALTERA_CLK -clock_fall 3 [get_ports altera_reserved_tdi]
set_input_delay -clock ALTERA_CLK -clock_fall 3 [get_ports altera_reserved_tms]
# set_input_delay -clock ALTERA_CLK -clock_fall 3 [get_ports altera_reserved_ntrst]
set_output_delay -clock ALTERA_CLK 3 [get_ports altera_reserved_tdo]

# From Timequest cookbook
set_clock_groups -exclusive -group ALTERA_CLK
