# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Vladislav Valek
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set MI_ASYNC_BASE               "$OFM_PATH/comp/mi_tools/async"
set MI_SPLITTER_PLUS_GEN_BASE   "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set MFB_PIPE_BASE               "$OFM_PATH/comp/mfb_tools/flow/pipe"
set DMA_CALYPTE_BASE            "$OFM_PATH/comp/dma/dma_calypte"
set DMA_TEST_CORE_BASE          "$OFM_PATH/comp/dma/dma_calypte/comp/test_core"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"

lappend COMPONENTS [ list "MI_ASYNC"               $MI_ASYNC_BASE              "FULL" ]
lappend COMPONENTS [ list "MI_SPLITTER_PLUS_GEN"   $MI_SPLITTER_PLUS_GEN_BASE  "FULL" ]
lappend COMPONENTS [ list "MFB_PIPE"               $MFB_PIPE_BASE              "FULL" ]
lappend COMPONENTS [ list "DMA_CALYPTE"            $DMA_CALYPTE_BASE           "FULL" ]
lappend COMPONENTS [ list "DMA_TEST_CORE"          $DMA_TEST_CORE_BASE         "FULL" ]

lappend MOD "$ENTITY_BASE/dma_wrapper.vhd"
