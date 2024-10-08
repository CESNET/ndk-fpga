# qsfp.xdc
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): David Beneš <benes.david2000@seznam.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# QSFP MISC INTERFACES
# ==============================================================================

set_property PACKAGE_PIN A10     [get_ports {QSFP0_INT_N}]
set_property PACKAGE_PIN D10     [get_ports {QSFP1_INT_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP?_INT_N}]
                                                                 
set_property PACKAGE_PIN A9      [get_ports {QSFP0_LPMODE}]
set_property PACKAGE_PIN D9      [get_ports {QSFP1_LPMODE}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP?_LPMODE}]
set_property SLEW SLOW           [get_ports {QSFP?_LPMODE}]
set_property DRIVE 4             [get_ports {QSFP?_LPMODE}]
                                                                 
set_property PACKAGE_PIN B9      [get_ports {QSFP0_MODPRS_N}]
set_property PACKAGE_PIN E10     [get_ports {QSFP1_MODPRS_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP?_MODPRS_N}]
                                                                 
set_property PACKAGE_PIN A8      [get_ports {QSFP0_RESET_N}]
set_property PACKAGE_PIN C10     [get_ports {QSFP1_RESET_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP?_RESET_N}]
set_property DRIVE 4             [get_ports {QSFP?_RESET_N}]
set_property SLEW SLOW           [get_ports {QSFP?_RESET_N}]
                                                                 
set_property PACKAGE_PIN B8      [get_ports {QSFP0_SCL}]
set_property PACKAGE_PIN C9      [get_ports {QSFP1_SCL}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP?_SCL}]
set_property DRIVE 4             [get_ports {QSFP?_SCL}]
set_property SLEW SLOW           [get_ports {QSFP?_SCL}]
                                                                 
set_property PACKAGE_PIN B7      [get_ports {QSFP0_SDA}]
set_property PACKAGE_PIN D8      [get_ports {QSFP1_SDA}]
set_property IOSTANDARD LVCMOS33 [get_ports {QSFP?_SDA}]
set_property DRIVE 4             [get_ports {QSFP?_SDA}]
set_property SLEW SLOW           [get_ports {QSFP?_SDA}]

# ==============================================================================
# QSFP HIGH SPEED INTERFACES
# ==============================================================================

set_property package_pin W33  [get_ports {QSFP0_REFCLK_N}]
set_property package_pin W32  [get_ports {QSFP0_REFCLK_P}]
set_property package_pin P31  [get_ports {QSFP1_REFCLK_N}]
set_property package_pin P30  [get_ports {QSFP1_REFCLK_P}]
                                                            
create_clock -period 6.206    [get_ports QSFP0_REFCLK_P]
create_clock -period 6.206    [get_ports QSFP1_REFCLK_P]
 
set_property PACKAGE_PIN Y40 [get_ports {QSFP0_RX_N[0]}]
set_property PACKAGE_PIN Y39 [get_ports {QSFP0_RX_P[0]}]
set_property PACKAGE_PIN Y35 [get_ports {QSFP0_TX_N[0]}]
set_property PACKAGE_PIN Y34 [get_ports {QSFP0_TX_P[0]}]

set_property PACKAGE_PIN W42 [get_ports {QSFP0_RX_N[1]}]
set_property PACKAGE_PIN W41 [get_ports {QSFP0_RX_P[1]}]
set_property PACKAGE_PIN W37 [get_ports {QSFP0_TX_N[1]}]
set_property PACKAGE_PIN W36 [get_ports {QSFP0_TX_P[1]}]

set_property PACKAGE_PIN V40 [get_ports {QSFP0_RX_N[2]}]
set_property PACKAGE_PIN V39 [get_ports {QSFP0_RX_P[2]}]
set_property PACKAGE_PIN V35 [get_ports {QSFP0_TX_N[2]}]
set_property PACKAGE_PIN V34 [get_ports {QSFP0_TX_P[2]}]

set_property PACKAGE_PIN U42 [get_ports {QSFP0_RX_N[3]}]
set_property PACKAGE_PIN U41 [get_ports {QSFP0_RX_P[3]}]
set_property PACKAGE_PIN U37 [get_ports {QSFP0_TX_N[3]}]
set_property PACKAGE_PIN U36 [get_ports {QSFP0_TX_P[3]}]
                                                    
set_property PACKAGE_PIN M40 [get_ports {QSFP1_RX_N[0]}]
set_property PACKAGE_PIN M39 [get_ports {QSFP1_RX_P[0]}]
set_property PACKAGE_PIN M35 [get_ports {QSFP1_TX_N[0]}]
set_property PACKAGE_PIN M34 [get_ports {QSFP1_TX_P[0]}]

set_property PACKAGE_PIN L42 [get_ports {QSFP1_RX_N[1]}]
set_property PACKAGE_PIN L41 [get_ports {QSFP1_RX_P[1]}]
set_property PACKAGE_PIN L37 [get_ports {QSFP1_TX_N[1]}]
set_property PACKAGE_PIN L36 [get_ports {QSFP1_TX_P[1]}]

set_property PACKAGE_PIN K40 [get_ports {QSFP1_RX_N[2]}]
set_property PACKAGE_PIN K39 [get_ports {QSFP1_RX_P[2]}]
set_property PACKAGE_PIN K35 [get_ports {QSFP1_TX_N[2]}]
set_property PACKAGE_PIN K34 [get_ports {QSFP1_TX_P[2]}]

set_property PACKAGE_PIN J42 [get_ports {QSFP1_RX_N[3]}]
set_property PACKAGE_PIN J41 [get_ports {QSFP1_RX_P[3]}]
set_property PACKAGE_PIN J37 [get_ports {QSFP1_TX_N[3]}]
set_property PACKAGE_PIN J36 [get_ports {QSFP1_TX_P[3]}]
