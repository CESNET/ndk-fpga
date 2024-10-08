# card_const.tcl: Default parameters for a card (development only)
# Copyright (C) 2022 CESNET, z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# WARNING: The user should not deliberately change parameters in this file. For
# the description of this file, visit the Parametrization section in the
# documentation of the NDK-CORE repostiory

set CARD_NAME "FB4CGG3"

if {$env(ETH_PORTS) == 2} {
    set CARD_NAME "FB2CGG3"
}
# Achitecture of Clock generator
set CLOCK_GEN_ARCH "USP"
# Achitecture of PCIe module
set PCIE_MOD_ARCH "USP"
# Achitecture of SDM/SYSMON module
set SDM_SYSMON_ARCH "USP_IDCOMP"
# Boot controller type
set BOOT_TYPE 2
# Achitecture of Network module
if { $ETH_PORT_SPEED(0) == 100 } {
    set NET_MOD_ARCH "CMAC"
} elseif { $ETH_PORT_SPEED(0) == 40 && $EHIP_PORT_TYPE(0) == 0 } {
    set NET_MOD_ARCH "40GE"
} elseif { $ETH_PORT_SPEED(0) == 40 && $EHIP_PORT_TYPE(0) == 2 } {
    set NET_MOD_ARCH "CESNET_LL40GE"
} elseif { $ETH_PORT_SPEED(0) == 10 && $EHIP_PORT_TYPE(0) == 2 } {
    set NET_MOD_ARCH "CESNET_LL10GE"
} else {
    error "Unsupported Ethernet port speed $ETH_PORT_SPEED(0) !"
}


# Total number of QSFP cages
set QSFP_CAGES       $ETH_PORTS
# I2C address of each QSFP cage
set QSFP_I2C_ADDR(0) "0xA0"
set QSFP_I2C_ADDR(1) "0xA0"
set QSFP_I2C_ADDR(2) "0xA0"
set QSFP_I2C_ADDR(3) "0xA0"

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!(($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 3 && $PCIE_ENDPOINT_MODE == 0)
      || ($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 3 && $PCIE_ENDPOINT_MODE == 2)
      ) } {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen3x16  -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0
- 1xGen3x8LL -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=2"
}

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set TSU_FREQUENCY 322265625

set MEM_PORTS 2
