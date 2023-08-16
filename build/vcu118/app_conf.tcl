# app_conf.tcl: User parameters for fb4cgg3/fb2cgg3 card
# Copyright (C) 2023 CESNET z.s.p.o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: The detailed description of the usage of this file can be viewed in the
# Parametrizing section of the NDK-CORE documentation.

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------
set DMA_RX_CHANNELS      2
set DMA_TX_CHANNELS      2
# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true

set DMA_RX_FRAME_SIZE_MAX 8191
set DMA_TX_FRAME_SIZE_MAX 8191
set DMA_TX_DATA_PTR_W 13

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set PROJECT_NAME "NDK_MINIMAL"
set PROJECT_VARIANT "$ETH_PORT_SPEED(0)G$ETH_PORTS"
set PROJECT_VERSION [exec cat ../../VERSION]
