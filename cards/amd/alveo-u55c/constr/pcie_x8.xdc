# pcie_x8.xdc: adding lanes to the PCIe endpoint
# Copyright (C) 2023 CESNET z. s. p. o.
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: BSD-3-Clause OR Apache-2.0

set_property PACKAGE_PIN AP3     [get_ports {PCIE_RX_N[4]}]
set_property PACKAGE_PIN AP4     [get_ports {PCIE_RX_P[4]}]
set_property PACKAGE_PIN AR1     [get_ports {PCIE_RX_N[5]}]
set_property PACKAGE_PIN AR2     [get_ports {PCIE_RX_P[5]}]
set_property PACKAGE_PIN AT3     [get_ports {PCIE_RX_N[6]}]
set_property PACKAGE_PIN AT4     [get_ports {PCIE_RX_P[6]}]
set_property PACKAGE_PIN AU1     [get_ports {PCIE_RX_N[7]}]
set_property PACKAGE_PIN AU2     [get_ports {PCIE_RX_P[7]}]

set_property PACKAGE_PIN AR10    [get_ports {PCIE_TX_N[4]}]
set_property PACKAGE_PIN AR11    [get_ports {PCIE_TX_P[4]}]
set_property PACKAGE_PIN AR6     [get_ports {PCIE_TX_N[5]}]
set_property PACKAGE_PIN AR7     [get_ports {PCIE_TX_P[5]}]
set_property PACKAGE_PIN AT8     [get_ports {PCIE_TX_N[6]}]
set_property PACKAGE_PIN AT9     [get_ports {PCIE_TX_P[6]}]
set_property PACKAGE_PIN AU10    [get_ports {PCIE_TX_N[7]}]
set_property PACKAGE_PIN AU11    [get_ports {PCIE_TX_P[7]}]
