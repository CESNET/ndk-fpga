# app_conf.tcl: User parameters for card
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: The detailed description of the usage of this file can be viewed in the
# Parametrizing section of the NDK-CORE documentation.

# ------------------------------------------------------------------------------
# PCIe parameters (not all combinations work):
# ------------------------------------------------------------------------------
# Supported combinations for this card:
# 1x PCIe Gen4 x8x8 -- PCIE_GEN=4, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1 
# 1x PCIe Gen4 x16  -- PCIE_GEN=4, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0 (Note: default configuration)
# ------------------------------------------------------------------------------
# PCIe Generation (possible values: 4):
# 4 = PCIe Gen4 (Stratix 10 with P-Tile or Agilex)
set PCIE_GEN           4
# PCIe endpoints (possible values: 1, 2, 4):
# 1 = 1x PCIe x16 in one slot
# 2 = 2x PCIe x16 in two slot OR 2x PCIe x8 in one slot (bifurcation x8+x8)
# 4 = 4x PCIe x8 in two slots (bifurcation x8+x8)
set PCIE_ENDPOINTS     1
# PCIe endpoint mode (possible values: 0, 1):
# 0 = 1x16 lanes
# 1 = 2x8 lanes (bifurcation x8+x8)
set PCIE_ENDPOINT_MODE 0

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------
# The minimum number of RX/TX DMA channels for this card is 16.
set DMA_RX_CHANNELS      16
set DMA_TX_CHANNELS      16
# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set PROJECT_NAME "NDK_MINIMAL"
set PROJECT_VARIANT "$ETH_PORT_SPEED(0)G$ETH_PORTS"
set PROJECT_VERSION [exec cat ../../VERSION]
