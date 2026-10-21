# DevTree.tcl: Component DeviceTree file
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2025
#
# SPDX-License-Identifier: BSD-3-Clause

# 1. base - base address on MI bus
# 2. type - type of card
proc dts_boot_controller {base type} {
    set    ret ""

    append ret "boot_controller {"
    append ret "compatible = \"dynanic,versal_ps_bridge\";"
    append ret "reg = <$base 0x1000>;"

    append ret "};"
    return $ret
}
