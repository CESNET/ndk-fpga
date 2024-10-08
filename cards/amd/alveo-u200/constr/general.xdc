# general.xdc
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# BITSTREAM CONFIGURATION
# ==============================================================================

set_property CFGBVS GND                                [current_design]
set_property CONFIG_VOLTAGE 1.8                        [current_design]
set_property BITSTREAM.GENERAL.COMPRESS true           [current_design]
set_property BITSTREAM.CONFIG.CONFIGFALLBACK ENABLE    [current_design]
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN DISABLE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 63.8          [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR YES       [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4           [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE YES        [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN PULLUP         [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN Enable  [current_design]

set_operating_conditions -design_power_budget 160

# ==============================================================================
# GENERAL PINS
# ==============================================================================

set_property PACKAGE_PIN AU19    [get_ports {SYSCLK_P}]
set_property PACKAGE_PIN AV19    [get_ports {SYSCLK_N}]
set_property IOSTANDARD LVDS     [get_ports {SYSCLK*}]
create_clock -period 6.400       [get_ports {SYSCLK_P}]

set_property PACKAGE_PIN BC21    [get_ports {STATUS_LED[0]}]
set_property PACKAGE_PIN BB21    [get_ports {STATUS_LED[1]}]
set_property PACKAGE_PIN BA20    [get_ports {STATUS_LED[2]}]
set_property IOSTANDARD LVCMOS12 [get_ports {STATUS_LED*}]
set_property DRIVE 8             [get_ports {STATUS_LED*}]
set_property SLEW SLOW           [get_ports {STATUS_LED*}]

# Lock DNA_PORT2E to X0Y1 due to different Chip ID in each SLRs!!!
set_property LOC CONFIG_SITE_X0Y1 [get_cells cm_i/hwid_i/usp_g.dna_port_i]
