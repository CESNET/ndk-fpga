# user_const.tcl: User parameters for DK-DEV-1SDX-P card
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ==============================================================================
# PCIe parameters (not all combinations work):
# ==============================================================================
# Supported combinations for this card:
# 1x PCIe Gen4 x8x8 -- PCIE_GEN=4, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1 (Note: default configuration)
# 1x PCIe Gen4 x16  -- PCIE_GEN=4, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0 (Note: worse DMA performance)
# 2x PCIe Gen4 x8x8 -- PCIE_GEN=4, PCIE_ENDPOINTS=4, PCIE_ENDPOINT_MODE=1 (Note: only for DMA_400G_DEMO)
# ------------------------------------------------------------------------------
# PCIe Generation (possible values: 3, 4, 5):
# 3 = PCIe Gen3
# 4 = PCIe Gen4 (Stratix 10 with P-Tile or Agilex)
# 5 = PCIe Gen5 (Agilex with R-Tile)
set PCIE_GEN           4
# PCIe endpoints (possible values: 1, 2, 4):
# 1 = 1x PCIe x16 in one slot
# 2 = 2x PCIe x16 in two slot OR 2x PCIe x8 in one slot (bifurcation x8+x8)
# 4 = 4x PCIe x8 in two slots (bifurcation x8+x8)
set PCIE_ENDPOINTS     2
# PCIe endpoint mode (possible values: 0, 1):
# 0 = 1x16 lanes
# 1 = 2x8 lanes (bifurcation x8+x8)
set PCIE_ENDPOINT_MODE 1
# ------------------------------------------------------------------------------

# ==============================================================================
# DMA parameters:
# ==============================================================================
# If you do not have access to a non-public repository with DMA IP, set to false.
# If the DMA module is disabled, loopback will be implemented instead.
set DMA_ENABLE           true
# The minimum number of RX/TX DMA channels for this card is 16.
set DMA_RX_CHANNELS      16
set DMA_TX_CHANNELS      16
# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true
# Special example of 400G DMA, Ethernet is not connected to DMA and must be set 
# special PCIe config.: 2x PCIe Gen4 x8x8, requires PCIe expansion connector.
set DMA_400G_DEMO        false
# ------------------------------------------------------------------------------

# Other parameters:
# =================
set PROJECT_NAME "DK-DEV-1SDX-P"
#if { $PORT0_MODE != 0 } {
#    append PROJECT_NAME "_" [EthSpeed $PORT0_MODE] "GE"
#}
