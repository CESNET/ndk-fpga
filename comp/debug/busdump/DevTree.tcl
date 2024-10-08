# DevTree.tcl: Device Tree specification of component
# Copyright (C) 2018 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# 1. base - base address on MI bus
# 2. name - instantion name inside device tree hierarchy
proc dts_busdump {base name} {
    set    ret ""
    append ret "$name {"
    append ret "compatible = \"netcope,busdump\";"
    append ret "reg = <$base 0x200>;"
    append ret "};"
    return $ret
}
