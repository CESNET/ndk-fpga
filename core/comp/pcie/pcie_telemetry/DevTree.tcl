# DevTree.tcl: describes the PCIe telemetry component
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# The layout of the counters is not described here, software reads it from the
# configuration registers of the component so that the two can never disagree.
#
# 1. base      - base address on the MI bus
# 2. endpoints - number of monitored PCIe endpoints
proc dts_pcie_telemetry_mi {base endpoints} {
    set    ret ""
    append ret "pcie_telemetry_mi {"
    append ret "compatible = \"cesnet,ofm,pcie_telemetry_mi\";"
    append ret "version = <0x00010000>;"
    append ret "reg = <$base 0x10000>;"
    append ret "pcie-endpoints = <$endpoints>;"
    append ret "};"
    return $ret
}
