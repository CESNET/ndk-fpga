# pblock.xdc
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

create_pblock pblock_pcie_i
resize_pblock pblock_pcie_i -add CLOCKREGION_X0Y0:CLOCKREGION_X7Y0

add_cells_to_pblock pblock_pcie_i [get_cells [list {core_logic_i/pcie_i} {core_logic_i/dma_i}]] -clear_locs
