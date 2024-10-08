# general.xdc
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Bitstream configuration
set_property BITSTREAM.GENERAL.COMPRESS true            [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN enable   [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 8            [current_design]
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN div-1    [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE yes         [current_design]
set_property CONFIG_VOLTAGE 1.8                         [current_design]
#set_property CONFIG_MODE S_SELECTMAP16                 [current_design]

# Reference clock
# 300 MHz clock
set_property PACKAGE_PIN G31 [get_ports {REFCLK_P}]
set_property PACKAGE_PIN F31 [get_ports {REFCLK_N}]

create_clock -period 3.333 -name refclk [get_ports {REFCLK_P}]

# 125 MHz clock
# set_property PACKAGE_PIN AY24 [get_ports {REFCLK_P}]
# set_property PACKAGE_PIN AY23 [get_ports {REFCLK_N}]

# create_clock -period 8 -name refclk [get_ports {REFCLK_P}]

# Only for 300
set_property IOSTANDARD DIFF_SSTL12 [get_ports {REFCLK_P}]
set_property IOSTANDARD DIFF_SSTL12 [get_ports {REFCLK_N}]

# SPI interface
# set_property PACKAGE_PIN AW28 [get_ports {SF2_CLK}]
# set_property PACKAGE_PIN AY28 [get_ports {SF2_MOSI}]
# set_property PACKAGE_PIN AY26 [get_ports {SF2_MISO}]
# set_property PACKAGE_PIN AY27 [get_ports {SF2_NSS}]
# set_property IOSTANDARD LVCMOS18 [get_ports {SF2_CLK}]
# set_property IOSTANDARD LVCMOS18 [get_ports {SF2_MOSI}]
# set_property IOSTANDARD LVCMOS18 [get_ports {SF2_MISO}]
# set_property IOSTANDARD LVCMOS18 [get_ports {SF2_NSS}]
# set_property IOB TRUE [get_ports {SF2_CLK}]
# set_property IOB TRUE [get_ports {SF2_MOSI}]
# set_property IOB TRUE [get_ports {SF2_MISO}]
# set_property IOB TRUE [get_ports {SF2_NSS}]

# Status LEDs
set_property PACKAGE_PIN AT32 [get_ports {STATUS_LED[0]}]
set_property PACKAGE_PIN AV34 [get_ports {STATUS_LED[1]}]
set_property PACKAGE_PIN AY30 [get_ports {STATUS_LED[2]}]
set_property PACKAGE_PIN BB32 [get_ports {STATUS_LED[3]}]

# Other unconnected LEDs
#set_property PACKAGE_PIN BF32 [get_ports {}]
#set_property PACKAGE_PIN AU37 [get_ports {}]
#set_property PACKAGE_PIN AV36 [get_ports {}]
#set_property PACKAGE_PIN BA37 [get_ports {}]

set_property IOSTANDARD LVCMOS12    [get_ports -filter NAME=~STATUS_LED*]
set_property DRIVE 8                [get_ports -filter NAME=~STATUS_LED*]
set_false_path -to                  [get_ports -filter NAME=~STATUS_LED*]

# ETH LEDs controller interface
# set_property PACKAGE_PIN AN23 [get_ports QLED_LE]
# set_property PACKAGE_PIN AN22 [get_ports QLED_SDI]
# set_property PACKAGE_PIN AN21 [get_ports QLED_CLK]
# set_property IOSTANDARD LVCMOS18 [get_ports QLED_LE]
# set_property IOSTANDARD LVCMOS18 [get_ports QLED_SDI]
# set_property IOSTANDARD LVCMOS18 [get_ports QLED_CLK]

# Lock DNA_PORT2E to X0Y1 due to different Chip ID in each SLRs
set_property LOC CONFIG_SITE_X0Y1 [get_cells cm_i/hwid_i/usp_g.dna_port_i]
