# user_const.tcl: User parameters for DK-DEV-AGI027RES
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# PCIe parameters:
# ================
# PCIe endpoints (allowed values: 1, 2, 4):
# 1 = 1x PCIe x16 in one slot
# 2 = 2x PCIe x16 in two slot OR 2x PCIe x8 in one slot (bifurcation x8+x8)
# 4 = 4x PCIe x8 in two slot (bifurcation x8+x8)
set PCIE_ENDPOINTS     4
# PCIe endpoint mode (allowed values: 0, 1):
# 0 = 1x16 lanes
# 1 = 2x8 lanes (bifurcation x8+x8)
set PCIE_ENDPOINT_MODE 1

# DMA parameters:
# ===============
# If you do not have access to a non-public repository with DMA IP, set to false.
# If the DMA module is disabled, loopback will be implemented instead.
set DMA_ENABLE      true
# The minimum number of RX/TX DMA channels for this card is 32.
set DMA_RX_CHANNELS 32
set DMA_TX_CHANNELS 32

# Other parameters:
# =================

set PROJECT_NAME "DK-DEV-AGI027RES"
#if { $PORT0_MODE != 0 } {
#    append PROJECT_NAME "_" [EthSpeed $PORT0_MODE] "GE"
#}
