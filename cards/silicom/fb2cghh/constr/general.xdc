# general.xdc
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): David Beneš <benes.david2000@seznam.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# BITSTREAM CONFIGURATION
# ==============================================================================

set_property BITSTREAM.GENERAL.COMPRESS true            [current_design]
set_property CONFIG_MODE SPIx4                          [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4            [current_design]
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN disable  [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE YES         [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR Yes        [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN enable   [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 85.0           [current_design]

# ==============================================================================
# GENERAL PINS
# ==============================================================================

set_property PACKAGE_PIN B4      [get_ports {PPS_IN }]
set_property PACKAGE_PIN A3      [get_ports {PPS_OUT_EN }]
set_property PACKAGE_PIN A4      [get_ports {PPS_OUT }]
set_property IOSTANDARD LVCMOS33 [get_ports PPS_*]

set_property PACKAGE_PIN C4      [get_ports {QLED_SDI}]
set_property PACKAGE_PIN B3      [get_ports {QLED_LE}]
set_property PACKAGE_PIN G3      [get_ports {QLED_CLK}]
set_property IOSTANDARD LVCMOS33 [get_ports {QLED_*}]

set_property PACKAGE_PIN C5      [get_ports {LED_STATUS[0]}]
set_property PACKAGE_PIN C6      [get_ports {LED_STATUS[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {LED_STATUS*}]

set_property PACKAGE_PIN E7      [get_ports {REFCLK}]
set_property IOSTANDARD LVCMOS18 [get_ports {REFCLK}]

create_clock -period 20.000      [get_ports {REFCLK}]

set_property PACKAGE_PIN D7      [get_ports {SF2_MISO}]
set_property PACKAGE_PIN J4      [get_ports {SF2_NSS}]
set_property PACKAGE_PIN B6      [get_ports {SF2_CLK}]
set_property PACKAGE_PIN D5      [get_ports {SF2_MOSI}]
set_property PACKAGE_PIN H4      [get_ports {SF2_INT}]
set_property IOSTANDARD LVCMOS18 [get_ports {SF2_*}]
