# pcie.xdc
# Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property PACKAGE_PIN AD12 [get_ports {PCIE_SYSCLK_P}]
set_property PACKAGE_PIN AD11 [get_ports {PCIE_SYSCLK_N}]

set_property PACKAGE_PIN D2 [get_ports {PCIE_SYSRST_N}]
set_property IOSTANDARD LVCMOS33 [get_ports {PCIE_SYSRST_N}]

create_clock -period 10.000 -name pcie_clk_p -waveform {0.000 5.000} [get_ports {PCIE_SYSCLK_P}]

set_property PACKAGE_PIN AM4 [get_ports {PCIE_RX_P[0]}]
set_property PACKAGE_PIN AL2 [get_ports {PCIE_RX_P[1]}]
set_property PACKAGE_PIN AK4 [get_ports {PCIE_RX_P[2]}]
set_property PACKAGE_PIN AJ2 [get_ports {PCIE_RX_P[3]}]
set_property PACKAGE_PIN AH4 [get_ports {PCIE_RX_P[4]}]
set_property PACKAGE_PIN AG2 [get_ports {PCIE_RX_P[5]}]
set_property PACKAGE_PIN AF4 [get_ports {PCIE_RX_P[6]}]
set_property PACKAGE_PIN AE2 [get_ports {PCIE_RX_P[7]}]
set_property PACKAGE_PIN AD4 [get_ports {PCIE_RX_P[8]}]
set_property PACKAGE_PIN AC2 [get_ports {PCIE_RX_P[9]}]
set_property PACKAGE_PIN AB4 [get_ports {PCIE_RX_P[10]}]
set_property PACKAGE_PIN AA2 [get_ports {PCIE_RX_P[11]}]
set_property PACKAGE_PIN Y4 [get_ports {PCIE_RX_P[12]}]
set_property PACKAGE_PIN W2 [get_ports {PCIE_RX_P[13]}]
set_property PACKAGE_PIN V4 [get_ports {PCIE_RX_P[14]}]
set_property PACKAGE_PIN U2 [get_ports {PCIE_RX_P[15]}]

set_property PACKAGE_PIN AM3 [get_ports {PCIE_RX_N[0]}]
set_property PACKAGE_PIN AL1 [get_ports {PCIE_RX_N[1]}]
set_property PACKAGE_PIN AK3 [get_ports {PCIE_RX_N[2]}]
set_property PACKAGE_PIN AJ1 [get_ports {PCIE_RX_N[3]}]
set_property PACKAGE_PIN AH3 [get_ports {PCIE_RX_N[4]}]
set_property PACKAGE_PIN AG1 [get_ports {PCIE_RX_N[5]}]
set_property PACKAGE_PIN AF3 [get_ports {PCIE_RX_N[6]}]
set_property PACKAGE_PIN AE1 [get_ports {PCIE_RX_N[7]}]
set_property PACKAGE_PIN AD3 [get_ports {PCIE_RX_N[8]}]
set_property PACKAGE_PIN AC1 [get_ports {PCIE_RX_N[9]}]
set_property PACKAGE_PIN AB3 [get_ports {PCIE_RX_N[10]}]
set_property PACKAGE_PIN AA1 [get_ports {PCIE_RX_N[11]}]
set_property PACKAGE_PIN Y3 [get_ports {PCIE_RX_N[12]}]
set_property PACKAGE_PIN W1 [get_ports {PCIE_RX_N[13]}]
set_property PACKAGE_PIN V3 [get_ports {PCIE_RX_N[14]}]
set_property PACKAGE_PIN U1 [get_ports {PCIE_RX_N[15]}]

set_property PACKAGE_PIN AL6 [get_ports {PCIE_TX_P[0]}]
set_property PACKAGE_PIN AK8 [get_ports {PCIE_TX_P[1]}]
set_property PACKAGE_PIN AJ6 [get_ports {PCIE_TX_P[2]}]
set_property PACKAGE_PIN AH8 [get_ports {PCIE_TX_P[3]}]
set_property PACKAGE_PIN AG6 [get_ports {PCIE_TX_P[4]}]
set_property PACKAGE_PIN AF8 [get_ports {PCIE_TX_P[5]}]
set_property PACKAGE_PIN AE6 [get_ports {PCIE_TX_P[6]}]
set_property PACKAGE_PIN AD8 [get_ports {PCIE_TX_P[7]}]
set_property PACKAGE_PIN AC6 [get_ports {PCIE_TX_P[8]}]
set_property PACKAGE_PIN AB8 [get_ports {PCIE_TX_P[9]}]
set_property PACKAGE_PIN AA6 [get_ports {PCIE_TX_P[10]}]
set_property PACKAGE_PIN Y8 [get_ports {PCIE_TX_P[11]}]
set_property PACKAGE_PIN W6 [get_ports {PCIE_TX_P[12]}]
set_property PACKAGE_PIN V8 [get_ports {PCIE_TX_P[13]}]
set_property PACKAGE_PIN U6 [get_ports {PCIE_TX_P[14]}]
set_property PACKAGE_PIN T8 [get_ports {PCIE_TX_P[15]}]

set_property PACKAGE_PIN AL5 [get_ports {PCIE_TX_N[0]}]
set_property PACKAGE_PIN AK7 [get_ports {PCIE_TX_N[1]}]
set_property PACKAGE_PIN AJ5 [get_ports {PCIE_TX_N[2]}]
set_property PACKAGE_PIN AH7 [get_ports {PCIE_TX_N[3]}]
set_property PACKAGE_PIN AG5 [get_ports {PCIE_TX_N[4]}]
set_property PACKAGE_PIN AF7 [get_ports {PCIE_TX_N[5]}]
set_property PACKAGE_PIN AE5 [get_ports {PCIE_TX_N[6]}]
set_property PACKAGE_PIN AD7 [get_ports {PCIE_TX_N[7]}]
set_property PACKAGE_PIN AC5 [get_ports {PCIE_TX_N[8]}]
set_property PACKAGE_PIN AB7 [get_ports {PCIE_TX_N[9]}]
set_property PACKAGE_PIN AA5 [get_ports {PCIE_TX_N[10]}]
set_property PACKAGE_PIN Y7 [get_ports {PCIE_TX_N[11]}]
set_property PACKAGE_PIN W5 [get_ports {PCIE_TX_N[12]}]
set_property PACKAGE_PIN V7 [get_ports {PCIE_TX_N[13]}]
set_property PACKAGE_PIN U5 [get_ports {PCIE_TX_N[14]}]
set_property PACKAGE_PIN T7 [get_ports {PCIE_TX_N[15]}]

####################################################################################
# Processing System Peripherals IO Constraints
#####################################################################################

# set_property PACKAGE_PIN B2 [get_ports PS_PCIE_RST]
# set_property PACKAGE_PIN B1 [get_ports PS_PCIE_INT]
