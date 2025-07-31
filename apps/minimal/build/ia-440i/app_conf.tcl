# app_conf.tcl: User parameters for card
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: The detailed description of the usage of this file can be viewed in the
# Parametrizing section of the NDK-CORE documentation.

# NOTE: Use the PCIE_CONF make parameter to select the PCIe configuration.

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------

if {$env(DMA_TYPE) == 4} {
    # DMA Calypte not meet timing on R-Tile FPGAs with more than 16 channels.
    set DMA_RX_CHANNELS 16
    set DMA_TX_CHANNELS 16
} else {
    # 400G DMA Medusa requires at least 32 channels.
    set DMA_RX_CHANNELS 32
    set DMA_TX_CHANNELS 32
}

# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true

# ------------------------------------------------------------------------------
# Select debug parameters:
# ------------------------------------------------------------------------------
# Enables debug probes and counters in the DMA Module (Medusa)
set DMA_DEBUG_ENABLE       false
# Enables debug probes in the PCIe Module (PCIe Ctrl)
set PCIE_CTRL_DEBUG_ENABLE false

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set PROJECT_NAME "NDK_MINIMAL"
set PROJECT_VARIANT "$ETH_PORT_SPEED(0)G$ETH_PORTS"
set PROJECT_VERSION [exec cat ../../../../VERSION]
