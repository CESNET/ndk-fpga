# pcie_x4.xdc: Base constraints for PCIe
# Copyright (C) 2023 CESNET z. s. p. o.
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: BSD-3-Clause OR Apache-2.0

# set_property PACKAGE_PIN AL1     [get_ports {PCIE_RX_N[0]}]
# set_property PACKAGE_PIN AL2     [get_ports {PCIE_RX_P[0]}]
# set_property PACKAGE_PIN AM3     [get_ports {PCIE_RX_N[1]}]
# set_property PACKAGE_PIN AM4     [get_ports {PCIE_RX_P[1]}]
# set_property PACKAGE_PIN AN5     [get_ports {PCIE_RX_N[2]}]
# set_property PACKAGE_PIN AN6     [get_ports {PCIE_RX_P[2]}]
# set_property PACKAGE_PIN AN1     [get_ports {PCIE_RX_N[3]}]
# set_property PACKAGE_PIN AN2     [get_ports {PCIE_RX_P[3]}]
# 
# set_property PACKAGE_PIN AL10    [get_ports {PCIE_TX_N[0]}]
# set_property PACKAGE_PIN AL11    [get_ports {PCIE_TX_P[0]}]
# set_property PACKAGE_PIN AM8     [get_ports {PCIE_TX_N[1]}]
# set_property PACKAGE_PIN AM9     [get_ports {PCIE_TX_P[1]}]
# set_property PACKAGE_PIN AN10    [get_ports {PCIE_TX_N[2]}]
# set_property PACKAGE_PIN AN11    [get_ports {PCIE_TX_P[2]}]
# set_property PACKAGE_PIN AP8     [get_ports {PCIE_TX_N[3]}]
# set_property PACKAGE_PIN AP9     [get_ports {PCIE_TX_P[3]}]

set_property PACKAGE_PIN BF41    [get_ports PCIE_SYSRST_N]
set_property IOSTANDARD LVCMOS18 [get_ports PCIE_SYSRST_N]
set_property PULLTYPE PULLUP     [get_ports PCIE_SYSRST_N]

set_property PACKAGE_PIN AL15 [get_ports PCIE_SYSCLK0_P]
set_property PACKAGE_PIN AL14 [get_ports PCIE_SYSCLK0_N]

set_property PACKAGE_PIN AR14 [get_ports PCIE_SYSCLK1_N]
set_property PACKAGE_PIN AR15 [get_ports PCIE_SYSCLK1_P]

create_clock -period 10.000 -name pcie_clk0_p -waveform {0.000 5.000} [get_ports PCIE_SYSCLK0_P]
create_clock -period 10.000 -name pcie_clk1_p -waveform {0.000 5.000} [get_ports PCIE_SYSCLK1_P]


