# DevTree.tcl: Component DeviceTree file
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# 1. base - base address on MI bus
proc dts_frequency_counter {base} {
    set    ret ""

    append ret "clock_frequency_meter {"
    append ret "compatible = \"cesnet,ofm,frequency_counter\";"
    append ret "reg = <$base 32>;"
    append ret "version = <0x00000001>;"
    append ret "};"
    return $ret
}


