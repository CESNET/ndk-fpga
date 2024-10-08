# core_conf.tcl: Core parameters for NDK which can be set customly by the user
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Mandatory project parameters
set PROJECT_NAME ""

# NOTE: For detailed description about a purpose of this file, see the
# Parametrization section in the documentation of the NDK-CORE repository.

# ------------------------------------------------------------------------------
# ETH parameters:
# ------------------------------------------------------------------------------
# Number of Ethernet ports, must match number of items in list ETH_PORTS_SPEED!
set ETH_PORTS          4
# Speed for each one of the ETH_PORTS
# ETH_PORT_SPEED is an array where each index represents given ETH_PORT and
# each index has associated a required port speed.
# NOTE: at this moment, all ports must have same speed!
set ETH_PORT_SPEED(0)  100
set ETH_PORT_SPEED(1)  100
set ETH_PORT_SPEED(2)  100
set ETH_PORT_SPEED(3)  100
# Type of used IP core for each one of the ETH_PORTS
# FTILE_TYPE is an array where each index represents a given ETH_PORT and
# is associated with a required type of used IP core for this port.
# NOTE: at this moment, all ports must have the same type of used IP core!
# Options are: 0 which is used for F-tile IP core
#              1 which is used for F-tile Multirate IP core
set EHIP_PORT_TYPE(0)  0
set EHIP_PORT_TYPE(1)  0
set EHIP_PORT_TYPE(2)  0
set EHIP_PORT_TYPE(3)  0
# Number of channels for each one of the ETH_PORTS
# ETH_PORT_CHAN is an array where each index represents given ETH_PORT and
# each index has associated a required number of channels this port has.
# NOTE: at this moment, all ports must have same number of channels!
set ETH_PORT_CHAN(0)   1
set ETH_PORT_CHAN(1)   1
set ETH_PORT_CHAN(2)   1
set ETH_PORT_CHAN(3)   1
# Number of lanes for each one of the ETH_PORTS
# Typical values: 4 (QSFP), 8 (QSFP-DD)
set ETH_PORT_LANES(0)  4
set ETH_PORT_LANES(1)  4
set ETH_PORT_LANES(2)  4
set ETH_PORT_LANES(3)  4
# Maximum allowed size of RX frame in bytes for each one of the ETH_PORTS
# NOTE: ETH_PORT_RX_MTU = 16383 is maximum supported value!
set ETH_PORT_RX_MTU(0) 16383
set ETH_PORT_RX_MTU(1) 16383
set ETH_PORT_RX_MTU(2) 16383
set ETH_PORT_RX_MTU(3) 16383
# Maximum allowed size of TX frame in bytes for each one of the ETH_PORTS
# NOTE: ETH_PORT_TX_MTU = 16383 is maximum supported value!
set ETH_PORT_TX_MTU(0) 16383
set ETH_PORT_TX_MTU(1) 16383
set ETH_PORT_TX_MTU(2) 16383
set ETH_PORT_TX_MTU(3) 16383
# Ethernet streams mode. Options are:
#    0 = All ETH channels from one ETH port (QSFP) are merged to a single ETH
#        stream (MFB+MVB bus). This is the default mode.
#    1 = Each ETH channel is linked to an independent ETH stream (MFB+MVB bus).
set ETH_STREAMS_MODE   0
# Optional option to disable Ethernet MAC Lite modules. Dangerously!
set ETH_MAC_BYPASS     false
# Total number of QSFP cages
set QSFP_CAGES         4
# I2C address of each QSFP cage
set QSFP_I2C_ADDR(0)   "0xA0"
set QSFP_I2C_ADDR(1)   "0xA0"
set QSFP_I2C_ADDR(2)   "0xA0"
set QSFP_I2C_ADDR(3)   "0xA0"

# ------------------------------------------------------------------------------
# Application core parameters:
# ------------------------------------------------------------------------------
set APP_CORE_ENABLE true

# ------------------------------------------------------------------------------
# PCIe parameters (not all combinations work):
# ------------------------------------------------------------------------------
# PCIe Generation (possible values: 3, 4, 5):
# 3 = PCIe Gen3
# 4 = PCIe Gen4 (Stratix 10 with P-Tile or Agilex)
# 5 = PCIe Gen5 (Agilex with R-Tile)
set PCIE_GEN           4
# PCIe endpoints (possible values: 1, 2, 4):
# 1 = 1x PCIe x16 in one slot or 1x PCIe x8 in one slot
# 2 = 2x PCIe x16 in two slot OR 2x PCIe x8 in one slot (bifurcation x8+x8)
# 4 = 4x PCIe x8 in two slot (bifurcation x8+x8)
set PCIE_ENDPOINTS     1
# PCIe endpoint mode (possible values: 0, 1, 2):
# 0 = 1x16 lanes
# 1 = 2x8 lanes (bifurcation x8+x8)
# 2 = 1x8 Low-latenxy (Xilinx USP only)
set PCIE_ENDPOINT_MODE 1

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------
# Total number of DMA modules/streams in FW
set DMA_MODULES           1
# Total number of DMA channels in whole FW
set DMA_RX_CHANNELS       16
set DMA_TX_CHANNELS       16
# Maximum allowed size of DMA RX frame in bytes
# NOTE: DMA_RX_FRAME_SIZE_MAX = 16383 is maximum supported value!
set DMA_RX_FRAME_SIZE_MAX 16383
# Maximum allowed size of DMA TX frame in bytes
# NOTE: DMA_TX_FRAME_SIZE_MAX = 16383 is maximum supported value!
set DMA_TX_FRAME_SIZE_MAX 16383
# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true
# Widths of pointers for data/headers
set DMA_RX_DATA_PTR_W 16
set DMA_RX_HDR_PTR_W  16
set DMA_TX_DATA_PTR_W 16
# Enables the GEN_LOOP_SWITCH component for debugging and testing
set DMA_GEN_LOOP_EN true

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set TSU_ENABLE      false
# Generic value must be replaced for each card
set TSU_FREQUENCY   161132812

# Number of external memory ports
set MEM_PORTS       0
set HBM_PORTS       0

# ------------------------------------------------------------------------------
# Enables virtual debugging (Intel SignalTap / Xilinx ILA) without a JTAG cable:
# ------------------------------------------------------------------------------
#   -- Xilinx Virtual Cable: Debug Hub over PCI extended config space (as VSEC),
#      available on Xilinx UltraScale+.
#   -- Intel JTAG-Over-Protocol IP, available on all supported Intel FPGAs.
set VIRTUAL_DEBUG_ENABLE false

# Enables debug probes and counters in the DMA Module (Medusa)
set DMA_DEBUG_ENABLE       false
# Enables debug probes and counters in the PCIe Module (PCIe Core arch: USP and P-Tile)
set PCIE_CORE_DEBUG_ENABLE false
# Enables debug probes in the PCIe Module (PCIe Ctrl)
set PCIE_CTRL_DEBUG_ENABLE false

# Enables Timstamp limit demo/testing logic
set TS_DEMO_EN             false
