# card_conf.tcl: Default parameters for XpressSX AGI-FH400G
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
# 			 Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: For the detailed description of this file, visit the Parametrization section
# in the documentation of the NDK-CORE repository.
#
# Mandatory project parameters
set PROJECT_NAME ""

# ------------------------------------------------------------------------------
# ETH parameters:
# ------------------------------------------------------------------------------
# Number of Ethernet ports, must match number of items in list ETH_PORTS_SPEED !
set ETH_PORTS          1
# Speed for each one of the ETH_PORTS (allowed values: 400, 200, 100, 50, 40, 25, 10)
# ETH_PORT_SPEED is an array where each index represents given ETH_PORT and
# each index has associated a required port speed.
# NOTE: at this moment, all ports must have same speed !
set ETH_PORT_SPEED(0)  $env(ETH_PORT_SPEED)
# Number of channels for each one of the ETH_PORTS (allowed values: 1, 2, 4, 8)
# ETH_PORT_CHAN is an array where each index represents given ETH_PORT and
# each index has associated a required number of channels this port has.
# NOTE: at this moment, all ports must have same number of channels !
set ETH_PORT_CHAN(0)   $env(ETH_PORT_CHAN)
# Number of lanes for each one of the ETH_PORTS
# Typical values: 4 (QSFP), 8 (QSFP-DD)
set ETH_PORT_LANES(0)  8
# EHIP_PORT_TYPE is an array where each index represents given ETH_PORT and
# each index has associated a required type of IP core, which this port has.
# NOTE: at this moment, all ports must have same type of IP core !
set EHIP_PORT_TYPE(0)  $env(EHIP_PORT_TYPE)

# ------------------------------------------------------------------------------
# PCIe parameters (not all combinations work):
# ------------------------------------------------------------------------------
# Supported combinations for this card:
# 1x PCIe Gen5 x8x8 -- PCIE_GEN=5, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1
# 2x PCIe Gen4 x8x8 -- PCIE_GEN=4, PCIE_ENDPOINTS=4, PCIE_ENDPOINT_MODE=1 (Note: default configuration)
# 1x PCIe Gen4 x8x8 -- PCIE_GEN=4, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1 (Note: limited DMA performance)
# ------------------------------------------------------------------------------

# Set default PCIe configuration
set PCIE_CONF "2xGen4x8x8"
if { [info exist env(PCIE_CONF)] } {
    set PCIE_CONF $env(PCIE_CONF)
}

# Parsing PCIE_CONF string to list of parameters
set pcie_conf_list [ParsePcieConf $PCIE_CONF]

# PCIe Generation (possible values: 4, 5):
# 4 = PCIe Gen4 (Stratix 10 with P-Tile or Agilex)
# 5 = PCIe Gen5 (Agilex with R-Tile)
set PCIE_GEN           [lindex $pcie_conf_list 1]
# PCIe endpoints (possible values: 2, 4):
# 2 = 2x PCIe x16 in two slot OR 2x PCIe x8 in one slot (bifurcation x8+x8)
# 4 = 4x PCIe x8 in two slots (bifurcation x8+x8)
set PCIE_ENDPOINTS     [lindex $pcie_conf_list 0]
# PCIe endpoint mode (possible values: 1):
# 1 = 2x8 lanes (bifurcation x8+x8)
set PCIE_ENDPOINT_MODE [lindex $pcie_conf_list 2]

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------
# This variable can be set in COREs *.mk file or as a parameter when launching the make
set DMA_TYPE             $env(DMA_TYPE)
# The minimum number of RX/TX DMA channels for this card is 32.
set DMA_RX_CHANNELS      32
set DMA_TX_CHANNELS      32
# In blocking mode, packets are dropped only when the RX DMA channel is off.
# In non-blocking mode, packets are dropped whenever they cannot be sent.
set DMA_RX_BLOCKING_MODE true

# ------------------------------------------------------------------------------
# DDR4 parameters:
# ------------------------------------------------------------------------------
set MEM_PORTS 2

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set TSU_ENABLE true

set BOARD_REV $env(BOARD_REV)

set TEST_FW_PCIE1_ONBOARD_DDR4 false

