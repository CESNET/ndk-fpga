# pcie_half.xdc:
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property PACKAGE_PIN AL1     [get_ports {PCIE_RX_N[0]}]
set_property PACKAGE_PIN AL2     [get_ports {PCIE_RX_P[0]}]
set_property PACKAGE_PIN AM3     [get_ports {PCIE_RX_N[1]}]
set_property PACKAGE_PIN AM4     [get_ports {PCIE_RX_P[1]}]
set_property PACKAGE_PIN AN5     [get_ports {PCIE_RX_N[2]}]
set_property PACKAGE_PIN AN6     [get_ports {PCIE_RX_P[2]}]
set_property PACKAGE_PIN AN1     [get_ports {PCIE_RX_N[3]}]
set_property PACKAGE_PIN AN2     [get_ports {PCIE_RX_P[3]}]
set_property PACKAGE_PIN AP3     [get_ports {PCIE_RX_N[4]}]
set_property PACKAGE_PIN AP4     [get_ports {PCIE_RX_P[4]}]
set_property PACKAGE_PIN AR1     [get_ports {PCIE_RX_N[5]}]
set_property PACKAGE_PIN AR2     [get_ports {PCIE_RX_P[5]}]
set_property PACKAGE_PIN AT3     [get_ports {PCIE_RX_N[6]}]
set_property PACKAGE_PIN AT4     [get_ports {PCIE_RX_P[6]}]
set_property PACKAGE_PIN AU1     [get_ports {PCIE_RX_N[7]}]
set_property PACKAGE_PIN AU2     [get_ports {PCIE_RX_P[7]}]


set_property PACKAGE_PIN AL10    [get_ports {PCIE_TX_N[0]}]
set_property PACKAGE_PIN AL11    [get_ports {PCIE_TX_P[0]}]
set_property PACKAGE_PIN AM8     [get_ports {PCIE_TX_N[1]}]
set_property PACKAGE_PIN AM9     [get_ports {PCIE_TX_P[1]}]
set_property PACKAGE_PIN AN10    [get_ports {PCIE_TX_N[2]}]
set_property PACKAGE_PIN AN11    [get_ports {PCIE_TX_P[2]}]
set_property PACKAGE_PIN AP8     [get_ports {PCIE_TX_N[3]}]
set_property PACKAGE_PIN AP9     [get_ports {PCIE_TX_P[3]}]
set_property PACKAGE_PIN AR10    [get_ports {PCIE_TX_N[4]}]
set_property PACKAGE_PIN AR11    [get_ports {PCIE_TX_P[4]}]
set_property PACKAGE_PIN AR6     [get_ports {PCIE_TX_N[5]}]
set_property PACKAGE_PIN AR7     [get_ports {PCIE_TX_P[5]}]
set_property PACKAGE_PIN AT8     [get_ports {PCIE_TX_N[6]}]
set_property PACKAGE_PIN AT9     [get_ports {PCIE_TX_P[6]}]
set_property PACKAGE_PIN AU10    [get_ports {PCIE_TX_N[7]}]
set_property PACKAGE_PIN AU11    [get_ports {PCIE_TX_P[7]}]

set_property PACKAGE_PIN BF41    [get_ports {PCIE_SYSRST_N}]
set_property IOSTANDARD LVCMOS18 [get_ports {PCIE_SYSRST_N}]
set_property PULLUP true         [get_ports {PCIE_SYSRST_N}]

set_property PACKAGE_PIN AR15    [get_ports {PCIE_SYSCLK_P}]
set_property PACKAGE_PIN AR14    [get_ports {PCIE_SYSCLK_N}]

create_clock -period 10.000 -name pcie_clk_p -waveform {0.000 5.000} [get_ports {PCIE_SYSCLK_P}]
