# user_const.tcl: User parameters for DK-DEV-1SDX-P card
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# DMA parameters:
# ===============
# If you do not have access to a non-public repository with DMA IP, set to false.
# If the DMA module is disabled, loopback will be implemented instead.
set DMA_ENABLE           true
set DMA_RX_CHANNELS      16
set DMA_TX_CHANNELS      16
# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true
# Special example of 400G DMA, Ethernet is not connected to DMA.
set DMA_400G_DEMO        false
# if DMA_400G_DEMO=True then PCIE_ENDPOINTS must be 4!
set PCIE_ENDPOINTS       2

# Other parameters:
# =================
set PROJECT_NAME "DK-DEV-1SDX-P"
#if { $PORT0_MODE != 0 } {
#    append PROJECT_NAME "_" [EthSpeed $PORT0_MODE] "GE"
#}
