# qsfp.xdc
# Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# QSFP MANAGEMENT INTERFACE
# ==============================================================================

set_property PACKAGE_PIN B26     [get_ports {QSFP_INT_B[0]}]
set_property PACKAGE_PIN N24     [get_ports {QSFP_INT_B[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP_INT_B[*]}]

set_property PACKAGE_PIN G25     [get_ports {QSFP_LPMODE[0]}]
set_property PACKAGE_PIN H25     [get_ports {QSFP_LPMODE[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP_LPMODE[*]}]

set_property PACKAGE_PIN C25     [get_ports {QSFP_MODPRS_B[0]}]
set_property PACKAGE_PIN H28     [get_ports {QSFP_MODPRS_B[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP_MODPRS_B[*]}]

set_property PACKAGE_PIN A26     [get_ports {QSFP_RESET_B[0]}]
set_property PACKAGE_PIN B27     [get_ports {QSFP_RESET_B[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP_RESET_B[*]}]

set_property PACKAGE_PIN B25     [get_ports {QSFP_SCL[0]}]
set_property PACKAGE_PIN P27     [get_ports {QSFP_SCL[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP_SCL[*]}]

set_property PACKAGE_PIN F25     [get_ports {QSFP_SDA[0]}]
set_property PACKAGE_PIN R24     [get_ports {QSFP_SDA[1]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP_SDA[*]}]

# ==============================================================================
# QSFP LEDS
# ==============================================================================

set_property PACKAGE_PIN L24     [get_ports {QSFP0_LED[0]}]
set_property PACKAGE_PIN L25     [get_ports {QSFP0_LED[1]}]
set_property PACKAGE_PIN K27     [get_ports {QSFP0_LED[2]}]
set_property PACKAGE_PIN J27     [get_ports {QSFP0_LED[3]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP0_LED[*]}]

set_property PACKAGE_PIN K26     [get_ports {QSFP1_LED[0]}]
set_property PACKAGE_PIN J25     [get_ports {QSFP1_LED[1]}]
set_property PACKAGE_PIN C27     [get_ports {QSFP1_LED[2]}]
set_property PACKAGE_PIN B28     [get_ports {QSFP1_LED[3]}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP1_LED[*]}]

# ==============================================================================
# QSFP HIGH SPEED INTERFACES
# ==============================================================================

set_property PACKAGE_PIN N45    [get_ports {QSFP0_RX_P[0]}]
set_property PACKAGE_PIN N46    [get_ports {QSFP0_RX_N[0]}]
set_property PACKAGE_PIN R45    [get_ports {QSFP0_RX_P[1]}]
set_property PACKAGE_PIN R46    [get_ports {QSFP0_RX_N[1]}]
set_property PACKAGE_PIN U45    [get_ports {QSFP0_RX_P[2]}]
set_property PACKAGE_PIN U46    [get_ports {QSFP0_RX_N[2]}]
set_property PACKAGE_PIN W45    [get_ports {QSFP0_RX_P[3]}]
set_property PACKAGE_PIN W46    [get_ports {QSFP0_RX_N[3]}]

set_property PACKAGE_PIN K42    [get_ports {QSFP0_TX_P[0]}]
set_property PACKAGE_PIN K43    [get_ports {QSFP0_TX_N[0]}]
set_property PACKAGE_PIN M42    [get_ports {QSFP0_TX_P[1]}]
set_property PACKAGE_PIN M43    [get_ports {QSFP0_TX_N[1]}]
set_property PACKAGE_PIN P42    [get_ports {QSFP0_TX_P[2]}]
set_property PACKAGE_PIN P43    [get_ports {QSFP0_TX_N[2]}]
set_property PACKAGE_PIN T42    [get_ports {QSFP0_TX_P[3]}]
set_property PACKAGE_PIN T43    [get_ports {QSFP0_TX_N[3]}]

set_property PACKAGE_PIN E45    [get_ports {QSFP1_RX_P[0]}]
set_property PACKAGE_PIN E46    [get_ports {QSFP1_RX_N[0]}]
set_property PACKAGE_PIN G45    [get_ports {QSFP1_RX_P[1]}]
set_property PACKAGE_PIN G46    [get_ports {QSFP1_RX_N[1]}]
set_property PACKAGE_PIN J45    [get_ports {QSFP1_RX_P[2]}]
set_property PACKAGE_PIN J46    [get_ports {QSFP1_RX_N[2]}]
set_property PACKAGE_PIN L45    [get_ports {QSFP1_RX_P[3]}]
set_property PACKAGE_PIN L46    [get_ports {QSFP1_RX_N[3]}]

set_property PACKAGE_PIN B42    [get_ports {QSFP1_TX_P[0]}]
set_property PACKAGE_PIN B43    [get_ports {QSFP1_TX_N[0]}]
set_property PACKAGE_PIN D42    [get_ports {QSFP1_TX_P[1]}]
set_property PACKAGE_PIN D43    [get_ports {QSFP1_TX_N[1]}]
set_property PACKAGE_PIN F42    [get_ports {QSFP1_TX_P[2]}]
set_property PACKAGE_PIN F43    [get_ports {QSFP1_TX_N[2]}]
set_property PACKAGE_PIN H42    [get_ports {QSFP1_TX_P[3]}]
set_property PACKAGE_PIN H43    [get_ports {QSFP1_TX_N[3]}]

set_property PACKAGE_PIN V38    [get_ports QSFP0_REFCLK_P]
set_property PACKAGE_PIN V39    [get_ports QSFP0_REFCLK_N]

set_property PACKAGE_PIN R40    [get_ports QSFP1_REFCLK_P]
set_property PACKAGE_PIN R41    [get_ports QSFP1_REFCLK_N]
