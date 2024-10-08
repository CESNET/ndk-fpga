# qsfp.xdc
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# QSFP MISC INTERFACES
# ==============================================================================

set_property PACKAGE_PIN BE21    [get_ports {QSFP0_INT_N}]
set_property PACKAGE_PIN AV21    [get_ports {QSFP1_INT_N}]
set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_INT_N}]
set_property PULLUP true         [get_ports {QSFP?_INT_N}]
                                                                 
set_property PACKAGE_PIN BD18    [get_ports {QSFP0_LPMODE}]
set_property PACKAGE_PIN AV22    [get_ports {QSFP1_LPMODE}]
set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_LPMODE}]
set_property SLEW SLOW           [get_ports {QSFP?_LPMODE}]
set_property DRIVE 8             [get_ports {QSFP?_LPMODE}]
                                                                 
set_property PACKAGE_PIN BE20    [get_ports {QSFP0_MODPRS_N}]
set_property PACKAGE_PIN BC19    [get_ports {QSFP1_MODPRS_N}]
set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_MODPRS_N}]
set_property PULLUP true         [get_ports {QSFP?_MODPRS_N}]
                                                                 
set_property PACKAGE_PIN BE17    [get_ports {QSFP0_RESET_N}]
set_property PACKAGE_PIN BC18    [get_ports {QSFP1_RESET_N}]
set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_RESET_N}]
set_property DRIVE 8             [get_ports {QSFP?_RESET_N}]
set_property SLEW SLOW           [get_ports {QSFP?_RESET_N}]

#set_property PACKAGE_PIN AT22    [get_ports {QSFP0_REFCLK_RESET}]
#set_property PACKAGE_PIN AR21    [get_ports {QSFP1_REFCLK_RESET}]
#set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_REFCLK_RESET}]
#set_property DRIVE 8             [get_ports {QSFP?_REFCLK_RESET}]
#set_property SLEW SLOW           [get_ports {QSFP?_REFCLK_RESET}]
#
#set_property PACKAGE_PIN AT20    [get_ports {QSFP0_FREQ_SEL[0]}]
#set_property PACKAGE_PIN AU22    [get_ports {QSFP0_FREQ_SEL[1]}]
#set_property PACKAGE_PIN AR22    [get_ports {QSFP1_FREQ_SEL[0]}]
#set_property PACKAGE_PIN AU20    [get_ports {QSFP1_FREQ_SEL[1]}]
#set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_FREQ_SEL[*]}]
#set_property SLEW SLOW           [get_ports {QSFP?_FREQ_SEL[*]}]
#set_property DRIVE 8             [get_ports {QSFP?_FREQ_SEL[*]}]

#TODO I2C                                                              
#set_property PACKAGE_PIN B8      [get_ports {QSFP0_SCL}]
#set_property PACKAGE_PIN C9      [get_ports {QSFP1_SCL}]
#set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_SCL}]
#set_property DRIVE 4             [get_ports {QSFP?_SCL}]
#set_property SLEW SLOW           [get_ports {QSFP?_SCL}]
#                                                                 
#set_property PACKAGE_PIN B7      [get_ports {QSFP0_SDA}]
#set_property PACKAGE_PIN D8      [get_ports {QSFP1_SDA}]
#set_property IOSTANDARD LVCMOS12 [get_ports {QSFP?_SDA}]
#set_property DRIVE 4             [get_ports {QSFP?_SDA}]
#set_property SLEW SLOW           [get_ports {QSFP?_SDA}]

# ==============================================================================
# QSFP HIGH SPEED INTERFACES
# ==============================================================================

set_property package_pin K11  [get_ports {QSFP0_REFCLK_P}]
set_property package_pin K10  [get_ports {QSFP0_REFCLK_N}]
create_clock -period 6.206    [get_ports {QSFP0_REFCLK_P}]

set_property package_pin P11  [get_ports {QSFP1_REFCLK_P}]
set_property package_pin P10  [get_ports {QSFP1_REFCLK_N}]
create_clock -period 6.206    [get_ports {QSFP1_REFCLK_P}]

set_property PACKAGE_PIN N4   [get_ports {QSFP0_RX_P[0]}]
set_property PACKAGE_PIN N3   [get_ports {QSFP0_RX_N[0]}]
set_property PACKAGE_PIN M2   [get_ports {QSFP0_RX_P[1]}]
set_property PACKAGE_PIN M1   [get_ports {QSFP0_RX_N[1]}]
set_property PACKAGE_PIN L4   [get_ports {QSFP0_RX_P[2]}]
set_property PACKAGE_PIN L3   [get_ports {QSFP0_RX_N[2]}]
set_property PACKAGE_PIN K2   [get_ports {QSFP0_RX_P[3]}]
set_property PACKAGE_PIN K1   [get_ports {QSFP0_RX_N[3]}]

set_property PACKAGE_PIN N9   [get_ports {QSFP0_TX_P[0]}]
set_property PACKAGE_PIN N8   [get_ports {QSFP0_TX_N[0]}]
set_property PACKAGE_PIN M7   [get_ports {QSFP0_TX_P[1]}]
set_property PACKAGE_PIN M6   [get_ports {QSFP0_TX_N[1]}]
set_property PACKAGE_PIN L9   [get_ports {QSFP0_TX_P[2]}]
set_property PACKAGE_PIN L8   [get_ports {QSFP0_TX_N[2]}]
set_property PACKAGE_PIN K7   [get_ports {QSFP0_TX_P[3]}]
set_property PACKAGE_PIN K6   [get_ports {QSFP0_TX_N[3]}]

set_property PACKAGE_PIN U4   [get_ports {QSFP1_RX_P[0]}]
set_property PACKAGE_PIN U3   [get_ports {QSFP1_RX_N[0]}]
set_property PACKAGE_PIN T2   [get_ports {QSFP1_RX_P[1]}]
set_property PACKAGE_PIN T1   [get_ports {QSFP1_RX_N[1]}]
set_property PACKAGE_PIN R4   [get_ports {QSFP1_RX_P[2]}]
set_property PACKAGE_PIN R3   [get_ports {QSFP1_RX_N[2]}]
set_property PACKAGE_PIN P2   [get_ports {QSFP1_RX_P[3]}]
set_property PACKAGE_PIN P1   [get_ports {QSFP1_RX_N[3]}]

set_property PACKAGE_PIN U9   [get_ports {QSFP1_TX_P[0]}]
set_property PACKAGE_PIN U8   [get_ports {QSFP1_TX_N[0]}]
set_property PACKAGE_PIN T7   [get_ports {QSFP1_TX_P[1]}]
set_property PACKAGE_PIN T6   [get_ports {QSFP1_TX_N[1]}]
set_property PACKAGE_PIN R9   [get_ports {QSFP1_TX_P[2]}]
set_property PACKAGE_PIN R8   [get_ports {QSFP1_TX_N[2]}]
set_property PACKAGE_PIN P7   [get_ports {QSFP1_TX_P[3]}]
set_property PACKAGE_PIN P6   [get_ports {QSFP1_TX_N[3]}]
