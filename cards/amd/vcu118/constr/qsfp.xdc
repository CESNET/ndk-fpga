# qsfp.xdc
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# QSFP port 0 ----------------------------------------------------
set_property PACKAGE_PIN W9 [get_ports {QSFP0_REFCLK_P}]
set_property PACKAGE_PIN W8 [get_ports {QSFP0_REFCLK_N}]

set_property PACKAGE_PIN Y2 [get_ports {QSFP0_RX_P[0]}]
set_property PACKAGE_PIN Y1 [get_ports {QSFP0_RX_N[0]}]
set_property PACKAGE_PIN W4 [get_ports {QSFP0_RX_P[1]}]
set_property PACKAGE_PIN W3 [get_ports {QSFP0_RX_N[1]}]
set_property PACKAGE_PIN V2 [get_ports {QSFP0_RX_P[2]}]
set_property PACKAGE_PIN V1 [get_ports {QSFP0_RX_N[2]}]
set_property PACKAGE_PIN U4 [get_ports {QSFP0_RX_P[3]}]
set_property PACKAGE_PIN U3 [get_ports {QSFP0_RX_N[3]}]

set_property PACKAGE_PIN V7 [get_ports {QSFP0_TX_P[0]}]
set_property PACKAGE_PIN V6 [get_ports {QSFP0_TX_N[0]}]
set_property PACKAGE_PIN T7 [get_ports {QSFP0_TX_P[1]}]
set_property PACKAGE_PIN T6 [get_ports {QSFP0_TX_N[1]}]
set_property PACKAGE_PIN P7 [get_ports {QSFP0_TX_P[2]}]
set_property PACKAGE_PIN P6 [get_ports {QSFP0_TX_N[2]}]
set_property PACKAGE_PIN M7 [get_ports {QSFP0_TX_P[3]}]
set_property PACKAGE_PIN M6 [get_ports {QSFP0_TX_N[3]}]

# QSFP port 1 ----------------------------------------------------
set_property PACKAGE_PIN R9 [get_ports {QSFP1_REFCLK_P}]
set_property PACKAGE_PIN R8 [get_ports {QSFP1_REFCLK_N}]

set_property PACKAGE_PIN T2 [get_ports {QSFP1_RX_P[0]}]
set_property PACKAGE_PIN T1 [get_ports {QSFP1_RX_N[0]}]
set_property PACKAGE_PIN R4 [get_ports {QSFP1_RX_P[1]}]
set_property PACKAGE_PIN R3 [get_ports {QSFP1_RX_N[1]}]
set_property PACKAGE_PIN P2 [get_ports {QSFP1_RX_P[2]}]
set_property PACKAGE_PIN P1 [get_ports {QSFP1_RX_N[2]}]
set_property PACKAGE_PIN M2 [get_ports {QSFP1_RX_P[3]}]
set_property PACKAGE_PIN M1 [get_ports {QSFP1_RX_N[3]}]

set_property PACKAGE_PIN L5 [get_ports {QSFP1_TX_P[0]}]
set_property PACKAGE_PIN L4 [get_ports {QSFP1_TX_N[0]}]
set_property PACKAGE_PIN K7 [get_ports {QSFP1_TX_P[1]}]
set_property PACKAGE_PIN K6 [get_ports {QSFP1_TX_N[1]}]
set_property PACKAGE_PIN J5 [get_ports {QSFP1_TX_P[2]}]
set_property PACKAGE_PIN J4 [get_ports {QSFP1_TX_N[2]}]
set_property PACKAGE_PIN H7 [get_ports {QSFP1_TX_P[3]}]
set_property PACKAGE_PIN H6 [get_ports {QSFP1_TX_N[3]}]

# QSFP misc ---------------------------------------------------
#set_property PACKAGE_PIN AR23 [get_ports {QSFP0_SCL}]
#set_property PACKAGE_PIN AT22 [get_ports {QSFP0_SDA}]
set_property PACKAGE_PIN BA22 [get_ports {QSFP0_RESET_N}]
set_property PACKAGE_PIN AL21 [get_ports {QSFP0_MODPRS_N}]
set_property PACKAGE_PIN AP21 [get_ports {QSFP0_INT_N}]
set_property PACKAGE_PIN AN21 [get_ports {QSFP0_LPMODE}]

#set_property PACKAGE_PIN BF22 [get_ports {QSFP1_SCL}]
#set_property PACKAGE_PIN BE22 [get_ports {QSFP1_SDA}]
set_property PACKAGE_PIN AY22 [get_ports {QSFP1_RESET_N}]
set_property PACKAGE_PIN AN24 [get_ports {QSFP1_MODPRS_N}]
set_property PACKAGE_PIN AT21 [get_ports {QSFP1_INT_N}]
set_property PACKAGE_PIN AT24 [get_ports {QSFP1_LPMODE}]

#set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_SCL}]
#set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_SDA}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_RESET_N}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_MODPRS_N}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_INT_N}]
set_property IOSTANDARD LVCMOS18 [get_ports {QSFP*_LPMODE}]
