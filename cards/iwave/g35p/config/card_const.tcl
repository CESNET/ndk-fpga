# card_const.tcl: Card specific parameters (developer only)
# Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause


# WARNING: The user should not deliberately change parameters in this file. For
# the description of this file, visit the Parametrization section in the
# documentation of the NDK-CORE repostiory

set CARD_NAME "IWAVE-G35P"
# Achitecture of Clock generator
set CLOCK_GEN_ARCH "USP"
# Achitecture of PCIe module
set PCIE_MOD_ARCH "USP"
# Achitecture of SDM/SYSMON module
# TODO: ZYNQ_ULTRASCALE
set SDM_SYSMON_ARCH "EMPTY"
# Boot controller type
set BOOT_TYPE 0
# Total number of DMA endpoints (one or two DMA endpoints per PCIe endpoint)
set DMA_ENDPOINTS $PCIE_ENDPOINTS
# Achitecture of Network module
set NET_MOD_ARCH "CMAC"

# Total number of QSFP cages
set QSFP_CAGES       2
# I2C address of each QSFP cage - There is no I2C connected to the QSFP cages (they are set to pull-up).
set QSFP_I2C_ADDR(0) "0xA0"
set QSFP_I2C_ADDR(1) "0xA0"

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 3 && $PCIE_ENDPOINT_MODE == 0) } {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen3x16  -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0"
}

if {!($MEM_PORTS == 0) } {
    error "Incompatible MEM_PORTS configuration: MEM_PORTS = $MEM_PORTS!
Allowed MEM_PORTS configurations:
- MEM_PORTS=0 -- External memory disabled, memory controllers are not instantiated."
}

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set TSU_FREQUENCY 322265625
