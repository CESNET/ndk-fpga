# card_const.tcl: Default parameters for card
# Copyright (C) 2024 CESNET, z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# WARNING: The user should not deliberately change parameters in this file. For
# the description of this file, visit the Parametrization section in the
# documentation of the NDK-CORE repostiory

set CARD_NAME "IA-440I"
# Achitecture of Clock generator (INTEL or USP)
set CLOCK_GEN_ARCH "INTEL"
# Achitecture of PCIe module (P_TILE, R_TILE or USP)
set PCIE_MOD_ARCH "R_TILE"
# Achitecture of Network module (E_TILE, F_TILE, CMAC or EMPTY)
set NET_MOD_ARCH "F_TILE"
# Achitecture of SDM/SYSMON module
set SDM_SYSMON_ARCH "INTEL_SDM"
# Boot controller type
set BOOT_TYPE 0
# Total number of DMA modules/streams in FW
set DMA_MODULES 1

# Total number of QSFP cages
set QSFP_CAGES 1
# I2C address of each QSFP cage
set QSFP_I2C_ADDR(0) "0xA0"
set QSFP_I2C_CUSTOM_CTRLS [list "i2c_bmc"]

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!(($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 4 && $PCIE_ENDPOINT_MODE == 0) ||
      ($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 5 && $PCIE_ENDPOINT_MODE == 0) ||
      ($PCIE_ENDPOINTS == 2 && $PCIE_GEN == 5 && $PCIE_ENDPOINT_MODE == 1)) } {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen4x16  -- PCIE_GEN=4, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0 (for DMA Calypte)
- 1xGen5x16  -- PCIE_GEN=5, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0 (for DMA Medusa)
- 1xGen5x8x8 -- PCIE_GEN=5, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1 (for DMA Medusa)"
}

if {!(($MEM_PORTS == 0) || ($MEM_PORTS == 2)) } {
    error "Unsupported value MEM_PORTS=$MEM_PORTS. Allowed values are only: 0 or 2."
}

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------

if {$ETH_PORT_SPEED(0) == 10 || $ETH_PORT_SPEED(0) == 25 || $ETH_PORT_SPEED(0) == 40} {
    # TBD lower frequency for 10GE, 40GE?
    #set TSU_FREQUENCY 161132812
    # Current setup:
    # 10GE, 25GE, 40GE in F-Tile
    set TSU_FREQUENCY 402832031
} else {
    # 400GE, 200GE, 100GE, 50GE in F-Tile
    set TSU_FREQUENCY 415039062
}
