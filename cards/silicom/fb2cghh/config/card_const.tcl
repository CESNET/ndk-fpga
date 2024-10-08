# card_const.tcl: Card specific parameters (developement only)
# Copyright (C) 2022 CESNET, z. s. p. o.
# Author(s): David Beneš     <xbenes52@vutbr.cz>
#            Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# WARNING: The user should not deliberately change parameters in this file. For
# the description of this file, visit the Parametrization section in the
# documentation of the NDK-CORE repostiory

set CARD_NAME "FB2CGHH"
# Achitecture of Clock generator
set CLOCK_GEN_ARCH "USP"
# Achitecture of PCIe module
set PCIE_MOD_ARCH "USP"
# Achitecture of SDM/SYSMON module
set SDM_SYSMON_ARCH "USP_IDCOMP"
# Boot controller type
set BOOT_TYPE 3
# Achitecture of Network module
if { $ETH_PORT_SPEED(0) == 100 } {
    set NET_MOD_ARCH "CMAC"
} elseif { $ETH_PORT_SPEED(0) == 40 } {
    set NET_MOD_ARCH "40GE"
} elseif { $ETH_PORT_SPEED(0) == 25 } {
    set NET_MOD_ARCH "25G4"
} elseif { $ETH_PORT_SPEED(0) == 10 } {
    set NET_MOD_ARCH "10G4"
} else {
    error "Unsupported Ethernet port speed $ETH_PORT_SPEED(0) !"
}

# Total number of QSFP cages
set QSFP_CAGES       2
# I2C address of each QSFP cage
set QSFP_I2C_ADDR(0) "0xA0"
set QSFP_I2C_ADDR(1) "0xA0"

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!(($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 3 && $PCIE_ENDPOINT_MODE == 0) ||
      ($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 3 && $PCIE_ENDPOINT_MODE == 2)) } {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen3x16  -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0
- 1xGen3x8LL -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=2"
}

if {!( ($MEM_PORTS == 0) || ($MEM_PORTS == 2)) } {
    error "Incompatible MEM_PORTS configuration: MEM_PORTS = $MEM_PORTS!
Allowed MEM_PORTS configurations:
- MEM_PORTS=0 -- External memory disabled, memory controllers are not instantiated.
- MEM_PORTS=2 -- External memory enabled, two DDR4 ports are available."
}

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set TSU_FREQUENCY 322265625
