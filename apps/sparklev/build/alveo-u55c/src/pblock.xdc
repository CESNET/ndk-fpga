# pblock.xdc
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

create_pblock pblock_pcie_i

add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -quiet [list axi_qspi_flash_i boot_ctrl_i]]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*DMA*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*PCIE*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*USER_CORE*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*ASYNC_OPEN_LOOP*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*RESET_TREE_GEN*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*ASYNC_RESET*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*MI_SPLITTER_PLUS_GEN*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*MI_TEST_SPACE*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*SDM_CTRL*" && PARENT =~  "core_logic_i" } ]
#add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*HWID*" && PARENT =~  "core_logic_i" } ]
add_cells_to_pblock [get_pblocks pblock_pcie_i] [get_cells -hierarchical -filter { REF_NAME =~  "*xpm_cdc_single*" && PARENT =~  "core_logic_i" } ]

resize_pblock [get_pblocks pblock_pcie_i] -add {SLICE_X230Y60:SLICE_X232Y239}
resize_pblock [get_pblocks pblock_pcie_i] -add {BUFG_GT_X1Y24:BUFG_GT_X1Y95}
resize_pblock [get_pblocks pblock_pcie_i] -add {BUFG_GT_SYNC_X1Y15:BUFG_GT_SYNC_X1Y59}
resize_pblock [get_pblocks pblock_pcie_i] -add {DSP48E2_X31Y18:DSP48E2_X31Y89}
resize_pblock [get_pblocks pblock_pcie_i] -add {CLOCKREGION_X0Y0:CLOCKREGION_X7Y0}

set_property CONTAIN_ROUTING 0 [get_pblocks pblock_pcie_i]
set_property IS_SOFT FALSE [get_pblocks pblock_pcie_i]
