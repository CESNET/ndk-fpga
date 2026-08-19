# app_conf.tcl: User parameters for Silicom ThunderFjord fb2cdg1 card
# Copyright (C) 2025 DynaNIC Semiconductors Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

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
# HBM parameters:
# ------------------------------------------------------------------------------
# allowed values 0 to 16

# HBM_PORTS are equally distributed between HBM_MODULES (must be divisible by two)
set HBM_PORTS        32
set HBM_MODULES      2
set HBM_DATA_WIDTH   512

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set PROJECT_NAME "NDK_MINIMAL"
set PROJECT_VARIANT "$ETH_PORT_SPEED(0)G$ETH_PORTS"
set PROJECT_VERSION [exec cat "$OFM_PATH/VERSION"]
