# general.xdc
# Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# BITSTREAM CONFIGURATION
# ==============================================================================

set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design]

set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN enable [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR No [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE Yes [current_design]
# Use external 80 MHz EMCCLK
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN Div-1 [current_design]

# ==============================================================================
# GENERAL PINS
# ==============================================================================

# System Clock for LOGIC (50 MHz)
set_property PACKAGE_PIN AK34     [get_ports SYSCLK]
set_property IOSTANDARD  LVCMOS18 [get_ports SYSCLK]
create_clock -period 20           [get_ports SYSCLK]

# QSPI flash interface for in-system bitstream updates:
#   The flash QSPI interface is multiplexed to 2 QSPI interfaces on the FPGA,
#   using a switch controlled by the BMC.
#   This in-system configuration QSPI port is active when the FPGA is programmed
#   (DONE=1) and no JTAG probe is active. Otherwise the native configuration
#   QSPI is selected.
set_property PACKAGE_PIN AR38     [get_ports SPI_CFG_CCLK]
set_property PACKAGE_PIN AR34     [get_ports {SPI_CFG_D[0]}]
set_property PACKAGE_PIN AR35     [get_ports {SPI_CFG_D[1]}]
set_property PACKAGE_PIN AR37     [get_ports {SPI_CFG_D[2]}]
set_property PACKAGE_PIN AP38     [get_ports {SPI_CFG_D[3]}]
set_property PACKAGE_PIN AP37     [get_ports SPI_CFG_FCS_B]
set_property IOSTANDARD LVCMOS18  [get_ports SPI_CFG_*]

# General-purpose front side LEDs
set_property PACKAGE_PIN D26      [get_ports TS_LED_GREEN]
set_property PACKAGE_PIN D27      [get_ports TS_LED_RED]
set_property IOSTANDARD LVCMOS18  [get_ports TS_LED_*]

# Debug LEDs
set_property PACKAGE_PIN R26      [get_ports {DEBUG_LED[0]}]
set_property PACKAGE_PIN M28      [get_ports {DEBUG_LED[1]}]
set_property PACKAGE_PIN R27      [get_ports {DEBUG_LED[2]}]
set_property PACKAGE_PIN T24      [get_ports {DEBUG_LED[3]}]
set_property IOSTANDARD LVCMOS18  [get_ports {DEBUG_LED[*]}]

# Lock DNA_PORT2E to X0Y0 due to different Chip ID in each SLRs!!!
set_property LOC CONFIG_SITE_X0Y0 [get_cells cm_i/hwid_i/usp_g.dna_port_i]
