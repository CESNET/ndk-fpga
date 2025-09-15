# app_conf.tcl: User parameters for target card
# Copyright (C) BrnoLogic, Ltd. - All Rights Reserved
# Author: Tomas Fukac <fukac@brnologic.com>, May 2024
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: The detailed description of the usage of this file can be viewed in the
# Parametrizing section of the NDK-CORE documentation.

# NOTE: Use the PCIE_CONF make parameter to select the PCIe configuration.

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------
# The minimum number of RX/TX DMA channels for this card is 32.
set DMA_RX_CHANNELS      32
set DMA_TX_CHANNELS      32
# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
# External DDR4 memory settings (allowed values 2 or 0).
set MEM_PORTS             0

# Set HBM ports, valid values are 0, 16 or 32
set HBM_PORTS            32

# Set number of DMA MODULES. Minimal design requires 4, otherwise 2 are fine.
set DMA_MODULES           4

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------

set PROJECT_NAME "NDK_MINIMAL"
set PROJECT_VARIANT "$ETH_PORT_SPEED(0)G$ETH_PORTS"
set PROJECT_VERSION [exec cat ../../../../VERSION]
