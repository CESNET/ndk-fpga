# card_const.tcl: Card specific parameters for Terasic A2700 (developer only)
# Copyright (C) 2024 BrnoLogic, Ltd.
# Author(s): David Beneš <benes@brnologic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# WARNING: The user should not deliberately change parameters in this file. For
# the description of this file, visit the Parametrization section in the
# documentation of the NDK-CORE repostiory

set CARD_NAME "TERASIC-A2700"
# Achitecture of Clock generator
set CLOCK_GEN_ARCH "INTEL"
# Achitecture of PCIe module
set PCIE_MOD_ARCH "R_TILE"
# Achitecture of Network module
set NET_MOD_ARCH "F_TILE"
# Achitecture of SDM/SYSMON module
set SDM_SYSMON_ARCH "INTEL_SDM"
# Boot controller type - SDM
set BOOT_TYPE 4

# Total number of QSFP cages
set QSFP_CAGES       1
# I2C address of each QSFP cage
set QSFP_I2C_ADDR(0) "0xA0"

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!(($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 4 && $PCIE_ENDPOINT_MODE == 0) ||
      ($PCIE_ENDPOINTS == 2 && $PCIE_GEN == 5 && $PCIE_ENDPOINT_MODE == 1)) } {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen4x16  -- PCIE_GEN=4, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0 (for DMA Calypte)
- 1xGen5x8x8 -- PCIE_GEN=5, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1 (for DMA Medusa)"
}

#DDR4
if {!($DDR4_PORTS == 0 || $DDR4_PORTS == 4) } {
    error "Unsupported number of DDR4_PORTS: Select either 0 or 4"
}

# Enable/add PCIe Gen5 x16 for experiments only!
#($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 5 && $PCIE_ENDPOINT_MODE == 0) ||
#- 1xGen5x16  -- PCIE_GEN=5, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0"

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
# Current setup is same for all IP cores, due to use of one pll with frequency (830,156Mhz), for all IP's:
# This setup value is defined as half of pll frequency
set TSU_FREQUENCY 415039062

setVhdlPkgInt DDR4_PORTS $DDR4_PORTS
