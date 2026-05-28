# app_conf.tcl: User parameters for Bittwaree IA-860m
# Copyright (C) 2025 DynaNIC Semiconductors Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: Use the PCIE_CONF make parameter to select the PCIe configuration.

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------

set DMA_RX_CHANNELS 32
set DMA_TX_CHANNELS 32

# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set PROJECT_NAME "NDK_MINIMAL"
set PROJECT_VARIANT "$ETH_PORT_SPEED(0)G$ETH_PORTS"
set PROJECT_VERSION [exec cat "$OFM_PATH/VERSION"]
