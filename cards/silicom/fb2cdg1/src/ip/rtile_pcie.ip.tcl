# rtile_pcie.ip.tcl: TCL script for generating R-Tile PCIe IP.
# Copyright (C) 2025 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

package require -exact qsys 21.3

array set PARAMS $IP_PARAMS_L
source $PARAMS(IP_COMMON_TCL)
source $PARAMS(IP_TEMPLATE_BASE)/pcie/rtile_pcie_conf_lib.tcl

set PCI_VENDOR_ID 0x18EC
set PCI_DEVICE_ID 0xC000
set USR_CLKFREQ 500MHz

load_system $PARAMS(IP_BUILD_DIR)/[get_ip_filename $PARAMS(IP_COMP_NAME)]
set_project_property DEVICE $PARAMS(IP_DEVICE)
set_project_property DEVICE_FAMILY $PARAMS(IP_DEVICE_FAMILY)
set_project_property HIDE_FROM_IP_CATALOG {true}

# common IP core parameters
do_rtile_pcie_common

# configuration-specific parameters
if {$PARAMS(PCIE_ENDPOINT_MODE) == 0 && $PARAMS(PCIE_GEN) == 4} {
    do_rtile_pcie_gen4_1x16 $PCI_VENDOR_ID $PCI_DEVICE_ID $USR_CLKFREQ
} elseif {$PARAMS(PCIE_ENDPOINT_MODE) == 0 && $PARAMS(PCIE_GEN) == 5} {
    do_rtile_pcie_gen5_1x16 $PCI_VENDOR_ID $PCI_DEVICE_ID $USR_CLKFREQ
} elseif {$PARAMS(PCIE_ENDPOINT_MODE) == 1 && $PARAMS(PCIE_GEN) == 5} {
    do_rtile_pcie_gen5_2x8 $PCI_VENDOR_ID $PCI_DEVICE_ID $USR_CLKFREQ
}

save_system $PARAMS(IP_COMP_NAME)
