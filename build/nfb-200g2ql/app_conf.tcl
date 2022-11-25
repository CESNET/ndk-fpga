# app_conf.tcl: User parameters for NFB-200G2QL card
# Copyright (C) 2022 CESNET z.s.p.o.
# Author(s): Daniel Kriz <danielkriz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: The detailed description of the usage of this file can be viewed in the
# Parametrizing section of the NDK-CORE documentation.

# ------------------------------------------------------------------------------
# PCIe parameters:
# ------------------------------------------------------------------------------
# Supported combinations for this card:
# 1x PCIe Gen3 x16 -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0
# 2x PCIe Gen3 x16 -- PCIE_GEN=3, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=0 (Note: default configuration)
# ------------------------------------------------------------------------------
# PCIe endpoints (possible values: 1, 2):
# 1 = 1x PCIe x16 in one slot
# 2 = 2x PCIe x16 in two slot
set PCIE_ENDPOINTS 2
# Other PCIe parameters are fixed.

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
