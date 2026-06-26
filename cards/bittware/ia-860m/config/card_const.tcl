# card_const.tcl: Card specific parameters for Silicom Bittwaree IA-860m
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Denis Kurka <kurka@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# WARNING: The user should not deliberately change parameters in this file. For
# the description of this file, visit the Parametrization section in the
# documentation of the NDK-CORE repostiory

set CARD_NAME        "IA-860M-VAR$BOARD_VARIANT"
# Achitecture of Clock generator
set CLOCK_GEN_ARCH   "INTEL"
# Achitecture of PCIe module
set PCIE_MOD_ARCH    "R_TILE"
# Achitecture of Network module (F_TILE)
set NET_MOD_ARCH     "F_TILE"
# Achitecture of SDM/SYSMON module
set SDM_SYSMON_ARCH  "INTEL_SDM"
# Boot controller type (5=OFS_PMCI)
set BOOT_TYPE        0
# Total number of DMA endpoints (one or two DMA endpoints per PCIe endpoint)
set DMA_ENDPOINTS [expr {$DMA_TYPE == 3 ? 4 : 1}]

# Total number of QSFP cages
set QSFP_CAGES       $env(ETH_PORTS)
# I2C address of each QSFP cage
# Each QSFP cage is connected by different I2C bus
set QSFP_I2C_ADDR(0) "0xA0"
set QSFP_I2C_ADDR(1) "0xA4"
if {$QSFP_CAGES == 3} {
    set QSFP_I2C_ADDR(2) "0xA8"
}

if {$BMC_ENABLE} {
    # This must be DISABLED when using simulation
    # Set custom I2C controllers for QSFP cages, connected to BMC I2C bus (same for all as there is only one BMC, which controls all QSFPs)
    if {$QSFP_CAGES == 3} {
        set QSFP_I2C_CUSTOM_CTRLS [list "i2c_bmc" "i2c_bmc" "i2c_bmc"]
    } elseif {$QSFP_CAGES == 2} {
        set QSFP_I2C_CUSTOM_CTRLS [list "i2c_bmc" "i2c_bmc"]
    }
}

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!(($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 4 && $PCIE_ENDPOINT_MODE == 0) ||
      ($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 5 && $PCIE_ENDPOINT_MODE == 0) ||
      ($PCIE_ENDPOINTS == 2 && $PCIE_GEN == 5 && $PCIE_ENDPOINT_MODE == 1) )} {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen4x16  -- PCIE_GEN=4, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0 (for DMA Calypte only)
- 1xGen5x16  -- PCIE_GEN=5, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0 (for DMA Medusa only)
- 1xGen5x8x8 -- PCIE_GEN=5, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1 (for DMA Medusa only)"
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
