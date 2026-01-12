# general.xdc
# Copyright (C) 2023 CESNET z. s. p. o.
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: BSD-3-Clause OR Apache-2.0

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

# System Clock for HBM (100 MHz) - onboard SYSCLK3 Clock
set_property PACKAGE_PIN BK44 [get_ports "HBM_REFCLK_N"];
set_property PACKAGE_PIN BK43 [get_ports "HBM_REFCLK_P"];
set_property IOSTANDARD  LVDS [get_ports "HBM_REFCLK_*"];
create_clock -period 10       [get_ports {HBM_REFCLK_P}]

# System Clock for LOGIC (100 MHz) - onboard SYSCLK2 Clock
set_property PACKAGE_PIN BL10 [get_ports "SYSCLK2_N"];
set_property PACKAGE_PIN BK10 [get_ports "SYSCLK2_P"];
set_property IOSTANDARD  LVDS [get_ports "SYSCLK2_*"];
create_clock -period 10       [get_ports {SYSCLK2_P}]

# HBM CATTRIP
set_property PACKAGE_PIN BE45     [get_ports "HBM_CATTRIP"];
set_property IOSTANDARD  LVCMOS18 [get_ports "HBM_CATTRIP"];

# Lock DNA_PORT2E to X0Y0 due to different Chip ID in each SLRs!!!
set_property LOC CONFIG_SITE_X0Y0 [get_cells core_logic_i/hwid_i/usp_g.dna_port_i]
