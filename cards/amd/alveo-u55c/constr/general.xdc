# general.xdc
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# BITSTREAM CONFIGURATION
# ==============================================================================

set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property BITSTREAM.CONFIG.CONFIGFALLBACK Enable [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property CONFIG_MODE SPIx4 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 63.8 [current_design]
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN disable [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE YES [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN Pullup [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR Yes [current_design]
set_operating_conditions -design_power_budget 100

# ==============================================================================
# GENERAL PINS
# ==============================================================================

# System Clock for LOGIC (100 MHz) - onboard SYSCLK3 Clock
set_property PACKAGE_PIN BK44 [get_ports "SYSCLK3_N"];
set_property PACKAGE_PIN BK43 [get_ports "SYSCLK3_P"];
set_property IOSTANDARD  LVDS [get_ports "SYSCLK3_*"];
create_clock -period 10       [get_ports {SYSCLK3_P}]

# System Clock for HBM (100 MHz) - onboard SYSCLK2 Clock
set_property PACKAGE_PIN BL10 [get_ports "SYSCLK2_N"];
set_property PACKAGE_PIN BK10 [get_ports "SYSCLK2_P"];
set_property IOSTANDARD  LVDS [get_ports "SYSCLK2_*"];
create_clock -period 10       [get_ports {SYSCLK2_P}]

# Alveo Satellite Controller (requires Alveo Card Management Solution IP)
set_property PACKAGE_PIN BJ42     [get_ports "MSP_UART_RXD"];
set_property PACKAGE_PIN BH42     [get_ports "MSP_UART_TXD"];
set_property IOSTANDARD  LVCMOS18 [get_ports "MSP_UART_*"];

set_property PACKAGE_PIN BF46     [get_ports "MSP_GPIO[3]"];
set_property PACKAGE_PIN BF45     [get_ports "MSP_GPIO[2]"];
set_property PACKAGE_PIN BH46     [get_ports "MSP_GPIO[1]"];
set_property PACKAGE_PIN BE46     [get_ports "MSP_GPIO[0]"];
set_property IOSTANDARD  LVCMOS18 [get_ports "MSP_GPIO"];

# HBM CATTRIP
set_property PACKAGE_PIN BE45     [get_ports "HBM_CATTRIP"];
set_property IOSTANDARD  LVCMOS18 [get_ports "HBM_CATTRIP"];

# Lock DNA_PORT2E to X0Y0 due to different Chip ID in each SLRs!!!
set_property LOC CONFIG_SITE_X0Y0 [get_cells cm_i/hwid_i/usp_g.dna_port_i]
