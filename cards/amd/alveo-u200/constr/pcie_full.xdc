# pcie_full.xdc: Adds second half of the connector pins when full x16 endpoint
# is used.
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property PACKAGE_PIN AP2     [get_ports {PCIE_RX_P[8]}]
set_property PACKAGE_PIN AP1     [get_ports {PCIE_RX_N[8]}]
set_property PACKAGE_PIN AR4     [get_ports {PCIE_RX_P[9]}]
set_property PACKAGE_PIN AR3     [get_ports {PCIE_RX_N[9]}]
set_property PACKAGE_PIN AT2     [get_ports {PCIE_RX_P[10]}]
set_property PACKAGE_PIN AT1     [get_ports {PCIE_RX_N[10]}]
set_property PACKAGE_PIN AU4     [get_ports {PCIE_RX_P[11]}]
set_property PACKAGE_PIN AU3     [get_ports {PCIE_RX_N[11]}]
set_property PACKAGE_PIN AV2     [get_ports {PCIE_RX_P[12]}]
set_property PACKAGE_PIN AV1     [get_ports {PCIE_RX_N[12]}]
set_property PACKAGE_PIN AW4     [get_ports {PCIE_RX_P[13]}]
set_property PACKAGE_PIN AW3     [get_ports {PCIE_RX_N[13]}]
set_property PACKAGE_PIN BA2     [get_ports {PCIE_RX_P[14]}]
set_property PACKAGE_PIN BA1     [get_ports {PCIE_RX_N[14]}]
set_property PACKAGE_PIN BC2     [get_ports {PCIE_RX_P[15]}]
set_property PACKAGE_PIN BC1     [get_ports {PCIE_RX_N[15]}]

set_property PACKAGE_PIN AP7     [get_ports {PCIE_TX_P[8]}]
set_property PACKAGE_PIN AP6     [get_ports {PCIE_TX_N[8]}]
set_property PACKAGE_PIN AR9     [get_ports {PCIE_TX_P[9]}]
set_property PACKAGE_PIN AR8     [get_ports {PCIE_TX_N[9]}]
set_property PACKAGE_PIN AT7     [get_ports {PCIE_TX_P[10]}]
set_property PACKAGE_PIN AT6     [get_ports {PCIE_TX_N[10]}]
set_property PACKAGE_PIN AU9     [get_ports {PCIE_TX_P[11]}]
set_property PACKAGE_PIN AU8     [get_ports {PCIE_TX_N[11]}]
set_property PACKAGE_PIN AV7     [get_ports {PCIE_TX_P[12]}]
set_property PACKAGE_PIN AV6     [get_ports {PCIE_TX_N[12]}]
set_property PACKAGE_PIN BB5     [get_ports {PCIE_TX_P[13]}]
set_property PACKAGE_PIN BB4     [get_ports {PCIE_TX_N[13]}]
set_property PACKAGE_PIN BD5     [get_ports {PCIE_TX_P[14]}]
set_property PACKAGE_PIN BD4     [get_ports {PCIE_TX_N[14]}]
set_property PACKAGE_PIN BF5     [get_ports {PCIE_TX_P[15]}]
set_property PACKAGE_PIN BF4     [get_ports {PCIE_TX_N[15]}]
