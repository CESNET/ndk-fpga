# core_funv.tcl: CORE TCL functions
# Copyright (C) 2023 CESNET, z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Parsing PCIE_CONF string to list of parameters (PCIE_EPS, PCIE_GEN, PCIE_MODE)
# Example 0: PCIE_CONF = "1xGen3x16"  returns: 1, 3, 0
# Example 1: PCIE_CONF = "2xGen5x16"  returns: 2, 5, 0
# Example 2: PCIE_CONF = "2xGen4x8x8" returns: 4, 4, 1
proc ParsePcieConf {PCIE_CONF} {
    set pcie_const0 0
    set pcie_const1 0
    set pcie_const2 0
    set pcie_eps 0
    set pcie_gen 0

    scan $PCIE_CONF {%d%[xX]%[a-zA-Z]%d%[a-zA-Z0-9]} pcie_eps pcie_const0 pcie_const1 pcie_gen pcie_const2

    if {$pcie_eps == 0} {
        error "Parsing error pcie_eps in PCIE_CONF = $PCIE_CONF! Don't know what to enter? \nTry this PCIe configuration: PCIE_CONF=1xGen4x16\n"
    }

    if {[string compare -nocase $pcie_const2 "x16"] == 0} {
        set pcie_mode 0
    } elseif {[string compare -nocase $pcie_const2 "x8x8"] == 0} {
        set pcie_mode 1
        set pcie_eps [expr 2 * $pcie_eps]
    } elseif {[string compare -nocase $pcie_const2 "x8LL"] == 0} {
        set pcie_mode 2
    } else {
        error "Parsing error PCIE_MODE in PCIE_CONF = $PCIE_CONF! Don't know what to enter? \nTry this PCIe configuration: PCIE_CONF=1xGen4x16\n"
    }
    return [list $pcie_eps $pcie_gen $pcie_mode]
}
