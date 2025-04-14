# pblock.xdc
# Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
# Author(s): David Beneš <benes@dyna-nic.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

create_pblock pblock_dma_i
resize_pblock pblock_dma_i -add CLOCKREGION_X3Y4:CLOCKREGION_X7Y7

add_cells_to_pblock pblock_dma_i [get_cells [list {cm_i/dma_i}]] -clear_locs

create_pblock pblock_pcie_i
resize_pblock pblock_pcie_i -add CLOCKREGION_X4Y0:CLOCKREGION_X7Y3

add_cells_to_pblock pblock_pcie_i [get_cells [list {cm_i/pcie_i}]] -clear_locs
