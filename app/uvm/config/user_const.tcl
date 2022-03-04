# user_const.tcl: Default parameters for NetCOPE@400G1
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Mandatory project parameters
set PROJECT_NAME ""

# User-defined generics
set USER_GENERIC0 0
set USER_GENERIC1 0
set USER_GENERIC2 0
set USER_GENERIC3 0

# ETH parameters:
# ===============
set ETH_ENABLE         false
# Number of Ethernet ports, must match number of items in list ETH_PORTS_SPEED !
set ETH_PORTS          1
# Speed for each one of the ETH_PORTS
# ETH_PORT_SPEED is an array where each index represents given ETH_PORT and
# each index has associated a required port speed.
# NOTE: at this moment, all ports must have same speed !
set ETH_PORT_SPEED(0)  400
# Number of channels for each one of the ETH_PORTS
# ETH_PORT_CHAN is an array where each index represents given ETH_PORT and
# each index has associated a required number of channels this port has.
# NOTE: at this moment, all ports must have same number of channels !
set ETH_PORT_CHAN(0)   1

# PCIe parameters:
# ================
# PCIe endpoints (allowed values: 1, 2, 4):
# 1 = 1x PCIe x16 in one slot
# 2 = 2x PCIe x16 in two slot OR 2x PCIe x8 in one slot (bifurcation x8+x8)
# 4 = 4x PCIe x8 in two slot (bifurcation x8+x8)
set PCIE_ENDPOINTS     1
# PCIe endpoint mode (allowed values: 0, 1):
# 0 = 1x16 lanes
# 1 = 2x8 lanes (bifurcation x8+x8)
set PCIE_ENDPOINT_MODE 1

# DMA parameters:
# ===============
# Type of DMA controllers: 0 = NDP; 3 = Packet on 400G arch
set DMA_ENABLE            true
set DMA_TYPE              3
set DMA_RX_CHANNELS       4
set DMA_TX_CHANNELS       4
set DMA_RX_BLOCKING_MODE  false
set DMA_TX_NDP_HDR_REMOVE true

# DMA CrossbarX clock selection
# 0 - Double of DMA CLK (400MHz)
# 1 - Same as DMA CLK (200MHz)
# 2 - Middle (300MHz)
set DMA_CROX_CLK_SEL     0

# Other parameters:
# =================
set TSU_ENABLE false
# Generic value must be replaced for each card
set TSU_FREQUENCY 161132812

# Manual control of registered reset signal replication for clocks domains of user clocks
#  - supported values from 1 to 16
set RESET_WIDTH 10
