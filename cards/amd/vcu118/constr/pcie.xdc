# pcie.xdc
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_false_path              -from [get_ports {PCIE_SYSRST_N}]
set_property PACKAGE_PIN AM17     [get_ports {PCIE_SYSRST_N}]
set_property IOSTANDARD  LVCMOS18 [get_ports {PCIE_SYSRST_N}]
set_property PULLUP      TRUE     [get_ports {PCIE_SYSRST_N}]

set_property PACKAGE_PIN AL9 [get_ports {PCIE_SYSCLK_P}]
set_property PACKAGE_PIN AL8 [get_ports {PCIE_SYSCLK_N}]

create_clock -name pci_clk -period 10 [get_ports {PCIE_SYSCLK_P}]

create_pblock pblock_pcie_i
set_property IS_SOFT TRUE [get_pblocks pblock_pcie_i]
resize_pblock [get_pblocks pblock_pcie_i] -add {CLOCKREGION_X5Y8:CLOCKREGION_X5Y5}
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -quiet [list cm_i/pcie_i cm_i/dma_i/dma_i]]
