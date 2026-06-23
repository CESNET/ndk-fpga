# card_const.tcl: Default parameters for card
# Copyright (C) 2023 CESNET, z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# WARNING: The user should not deliberately change parameters in this file. For
# the description of this file, visit the Parametrization section in the
# documentation of the NDK-CORE repostiory

set CARD_NAME "N5014"
# Achitecture of Clock generator (INTEL or USP)
set CLOCK_GEN_ARCH "INTEL"
# Achitecture of PCIe module (P_TILE, R_TILE or USP)
set PCIE_MOD_ARCH "P_TILE"
# Achitecture of Network module (E_TILE, F_TILE, CMAC or EMPTY)
set NET_MOD_ARCH "E_TILE"
# Achitecture of Soft network module (HITEK)
set CLV_MOD_ARCH "NONE"
# Achitecture of SDM/SYSMON module
set SDM_SYSMON_ARCH "INTEL_SDM"
# Boot controller type (5=OFS_PMCI/OFS_SPI)
set BOOT_TYPE 5
# Total number of DMA endpoints (one or two DMA endpoints per PCIe endpoint)
# NOTE: fpga_common does not support 2 region for MFB (100 Gbps) >> 2 DMA Streams are needed (2 DMA Modules)
#       2 Endpoints are set, but only 1 is used per DMA Module (division by 0 in rx_dma_medusa)
set DMA_ENDPOINTS [expr {($DMA_TYPE == 3) ? (($DMA_MODULES == 4) ? 4 : 2) : 1}]

# Total number of QSFP cages
set QSFP_CAGES       4
# I2C address of each QSFP cage
set QSFP_I2C_ADDR(0) "0xA0"
set QSFP_I2C_ADDR(1) "0xA0"
set QSFP_I2C_ADDR(2) "0xA0"
set QSFP_I2C_ADDR(3) "0xA0"

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!(($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 4 && $PCIE_ENDPOINT_MODE == 0)) } {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen4x16  -- PCIE_GEN=4, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0"
}

#if {!( ($MEM_PORTS == 0) || ($MEM_PORTS == 4)) } {
#    error "Incompatible MEM_PORTS configuration: MEM_PORTS = $MEM_PORTS!
#Allowed MEM_PORTS configurations:
#- MEM_PORTS=0 -- External memory disabled, memory controllers are not instantiated.
#- MEM_PORTS=4 -- External memory enabled, four DDR4 ports are available."
#}

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
if {$ETH_PORT_SPEED(0) == 10} {
    set TSU_FREQUENCY 161132812
} else {
    # 100GE and 25GE in E-Tile
    set TSU_FREQUENCY 402832031
}
