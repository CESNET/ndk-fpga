# general.xdc
# Copyright (C) 2022 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Bitstream configuration
set_property BITSTREAM.GENERAL.COMPRESS true [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN enable [current_design]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CONFIG_MODE S_SELECTMAP16 [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN enable [current_design]

# General pins
set_property PACKAGE_PIN AU22 [get_ports PPS_IN]
set_property PACKAGE_PIN AV22 [get_ports PPS_OUT]
set_property PACKAGE_PIN AV26 [get_ports REFCLK]
set_property IOSTANDARD LVCMOS18 [get_ports PPS_IN]
set_property IOSTANDARD LVCMOS18 [get_ports PPS_OUT]
set_property IOSTANDARD LVCMOS18 [get_ports REFCLK]
create_clock -period 20.000 -name refclk [get_ports REFCLK]

# SPI interface
set_property PACKAGE_PIN AW28 [get_ports SF2_CLK]
set_property PACKAGE_PIN AY28 [get_ports SF2_MOSI]
set_property PACKAGE_PIN AY26 [get_ports SF2_MISO]
set_property PACKAGE_PIN AY27 [get_ports SF2_NSS]
set_property IOSTANDARD LVCMOS18 [get_ports SF2_CLK]
set_property IOSTANDARD LVCMOS18 [get_ports SF2_MOSI]
set_property IOSTANDARD LVCMOS18 [get_ports SF2_MISO]
set_property IOSTANDARD LVCMOS18 [get_ports SF2_NSS]
set_property IOB TRUE [get_ports {SF2_CLK}]
set_property IOB TRUE [get_ports {SF2_MOSI}]
set_property IOB TRUE [get_ports {SF2_MISO}]
set_property IOB TRUE [get_ports {SF2_NSS}]

# Status LEDs
set_property PACKAGE_PIN AN24 [get_ports {STATUS_LED_G0}]
set_property PACKAGE_PIN AP24 [get_ports {STATUS_LED_R0}]
set_property PACKAGE_PIN AL24 [get_ports {STATUS_LED_G1}]
set_property PACKAGE_PIN AM24 [get_ports {STATUS_LED_R1}]
set_property IOSTANDARD LVCMOS18 [get_ports {STATUS_LED_G0}]
set_property IOSTANDARD LVCMOS18 [get_ports {STATUS_LED_R0}]
set_property IOSTANDARD LVCMOS18 [get_ports {STATUS_LED_G1}]
set_property IOSTANDARD LVCMOS18 [get_ports {STATUS_LED_R1}]

# ETH LEDs controller interface
set_property PACKAGE_PIN AN23 [get_ports QLED_LE]
set_property PACKAGE_PIN AN22 [get_ports QLED_SDI]
set_property PACKAGE_PIN AN21 [get_ports QLED_CLK]
set_property IOSTANDARD LVCMOS18 [get_ports QLED_LE]
set_property IOSTANDARD LVCMOS18 [get_ports QLED_SDI]
set_property IOSTANDARD LVCMOS18 [get_ports QLED_CLK]

# Lock DNA_PORT2E to X0Y1 due to different Chip ID in each SLRs
set_property LOC CONFIG_SITE_X0Y1 [get_cells usp_i/hwid_i/usp_g.dna_port_i]
