# pcie_x16.xdc: pinout for the PCIe lanes on a full endpoint
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property PACKAGE_PIN AV3     [get_ports {PCIE_RX_N[8]}]
set_property PACKAGE_PIN AV4     [get_ports {PCIE_RX_P[8]}]
set_property PACKAGE_PIN AW5     [get_ports {PCIE_RX_N[9]}]
set_property PACKAGE_PIN AW6     [get_ports {PCIE_RX_P[9]}]
set_property PACKAGE_PIN AW1     [get_ports {PCIE_RX_N[10]}]
set_property PACKAGE_PIN AW2     [get_ports {PCIE_RX_P[10]}]
set_property PACKAGE_PIN AY3     [get_ports {PCIE_RX_N[11]}]
set_property PACKAGE_PIN AY4     [get_ports {PCIE_RX_P[11]}]
set_property PACKAGE_PIN BA5     [get_ports {PCIE_RX_N[12]}]
set_property PACKAGE_PIN BA6     [get_ports {PCIE_RX_P[12]}]
set_property PACKAGE_PIN BA1     [get_ports {PCIE_RX_N[13]}]
set_property PACKAGE_PIN BA2     [get_ports {PCIE_RX_P[13]}]
set_property PACKAGE_PIN BB3     [get_ports {PCIE_RX_N[14]}]
set_property PACKAGE_PIN BB4     [get_ports {PCIE_RX_P[14]}]
set_property PACKAGE_PIN BC1     [get_ports {PCIE_RX_N[15]}]
set_property PACKAGE_PIN BC2     [get_ports {PCIE_RX_P[15]}]

set_property PACKAGE_PIN AU6     [get_ports {PCIE_TX_N[8]}]
set_property PACKAGE_PIN AU7     [get_ports {PCIE_TX_P[8]}]
set_property PACKAGE_PIN AV8     [get_ports {PCIE_TX_N[9]}]
set_property PACKAGE_PIN AV9     [get_ports {PCIE_TX_P[9]}]
set_property PACKAGE_PIN AW10    [get_ports {PCIE_TX_N[10]}]
set_property PACKAGE_PIN AW11    [get_ports {PCIE_TX_P[10]}]
set_property PACKAGE_PIN AY8     [get_ports {PCIE_TX_N[11]}]
set_property PACKAGE_PIN AY9     [get_ports {PCIE_TX_P[11]}]
set_property PACKAGE_PIN BA10    [get_ports {PCIE_TX_N[12]}]
set_property PACKAGE_PIN BA11    [get_ports {PCIE_TX_P[12]}]
set_property PACKAGE_PIN BB8     [get_ports {PCIE_TX_N[13]}]
set_property PACKAGE_PIN BB9     [get_ports {PCIE_TX_P[13]}]
set_property PACKAGE_PIN BC10    [get_ports {PCIE_TX_N[14]}]
set_property PACKAGE_PIN BC11    [get_ports {PCIE_TX_P[14]}]
set_property PACKAGE_PIN BC6     [get_ports {PCIE_TX_N[15]}]
set_property PACKAGE_PIN BC7     [get_ports {PCIE_TX_P[15]}]
