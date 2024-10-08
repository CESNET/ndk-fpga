# pcie_half.xdc: Adds base lanes of a PCIe x8 endpoint and also its clock
# which is used by every PCIe configuration.
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property PACKAGE_PIN AF2     [get_ports {PCIE_RX_P[0]}]
set_property PACKAGE_PIN AF1     [get_ports {PCIE_RX_N[0]}]
set_property PACKAGE_PIN AG4     [get_ports {PCIE_RX_P[1]}]
set_property PACKAGE_PIN AG3     [get_ports {PCIE_RX_N[1]}]
set_property PACKAGE_PIN AH2     [get_ports {PCIE_RX_P[2]}]
set_property PACKAGE_PIN AH1     [get_ports {PCIE_RX_N[2]}]
set_property PACKAGE_PIN AJ4     [get_ports {PCIE_RX_P[3]}]
set_property PACKAGE_PIN AJ3     [get_ports {PCIE_RX_N[3]}]
set_property PACKAGE_PIN AK2     [get_ports {PCIE_RX_P[4]}]
set_property PACKAGE_PIN AK1     [get_ports {PCIE_RX_N[4]}]
set_property PACKAGE_PIN AL4     [get_ports {PCIE_RX_P[5]}]
set_property PACKAGE_PIN AL3     [get_ports {PCIE_RX_N[5]}]
set_property PACKAGE_PIN AM2     [get_ports {PCIE_RX_P[6]}]
set_property PACKAGE_PIN AM1     [get_ports {PCIE_RX_N[6]}]
set_property PACKAGE_PIN AN4     [get_ports {PCIE_RX_P[7]}]
set_property PACKAGE_PIN AN3     [get_ports {PCIE_RX_N[7]}]

set_property PACKAGE_PIN AF7     [get_ports {PCIE_TX_P[0]}]
set_property PACKAGE_PIN AF6     [get_ports {PCIE_TX_N[0]}]
set_property PACKAGE_PIN AG9     [get_ports {PCIE_TX_P[1]}]
set_property PACKAGE_PIN AG8     [get_ports {PCIE_TX_N[1]}]
set_property PACKAGE_PIN AH7     [get_ports {PCIE_TX_P[2]}]
set_property PACKAGE_PIN AH6     [get_ports {PCIE_TX_N[2]}]
set_property PACKAGE_PIN AJ9     [get_ports {PCIE_TX_P[3]}]
set_property PACKAGE_PIN AJ8     [get_ports {PCIE_TX_N[3]}]
set_property PACKAGE_PIN AK7     [get_ports {PCIE_TX_P[4]}]
set_property PACKAGE_PIN AK6     [get_ports {PCIE_TX_N[4]}]
set_property PACKAGE_PIN AL9     [get_ports {PCIE_TX_P[5]}]
set_property PACKAGE_PIN AL8     [get_ports {PCIE_TX_N[5]}]
set_property PACKAGE_PIN AM7     [get_ports {PCIE_TX_P[6]}]
set_property PACKAGE_PIN AM6     [get_ports {PCIE_TX_N[6]}]
set_property PACKAGE_PIN AN9     [get_ports {PCIE_TX_P[7]}]
set_property PACKAGE_PIN AN8     [get_ports {PCIE_TX_N[7]}]

set_property PACKAGE_PIN BD21    [get_ports {PCIE_SYSRST_N}]
set_property IOSTANDARD LVCMOS12 [get_ports {PCIE_SYSRST_N}]
set_property PULLUP true         [get_ports {PCIE_SYSRST_N}]

set_property PACKAGE_PIN AM11    [get_ports {PCIE_SYSCLK_P}] 
set_property PACKAGE_PIN AM10    [get_ports {PCIE_SYSCLK_N}] 

create_clock -period 10.000 -name pcie_clk_p -waveform {0.000 5.000} [get_ports {PCIE_SYSCLK_P}]

create_pblock pblock_pcie_i
set_property IS_SOFT TRUE [get_pblocks pblock_pcie_i]
resize_pblock [get_pblocks pblock_pcie_i] -add {CLOCKREGION_X5Y8:CLOCKREGION_X5Y5}
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -quiet [list cm_i/pcie_i cm_i/dma_i/dma_i]]
