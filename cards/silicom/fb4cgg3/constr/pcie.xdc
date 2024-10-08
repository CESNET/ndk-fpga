# pcie.xdc
# Copyright (C) 2022 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property PACKAGE_PIN AR26     [get_ports {PCIE_SYSRST_N}]
set_property IOSTANDARD  LVCMOS18 [get_ports {PCIE_SYSRST_N}]
set_property PULLUP      TRUE     [get_ports {PCIE_SYSRST_N}]

set_property PACKAGE_PIN AT11 [get_ports {PCIE_SYSCLK_P}]
set_property PACKAGE_PIN AT10 [get_ports {PCIE_SYSCLK_N}]

create_clock -name pci_clk -period 10 [get_ports *PCIE_SYSCLK_P]

create_pblock pblock_pcie_i
resize_pblock [get_pblocks pblock_pcie_i] -add {SLR1}
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -quiet [list usp_i/pcie_i]]
