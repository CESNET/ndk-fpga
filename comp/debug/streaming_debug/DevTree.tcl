# DevTree.tcl: Device Tree specification of component
# Copyright (C) 2018 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# 1. base - base address on MI bus
# 2. name - instantion name inside device tree hierarchy
# 3. probes - number of probes connected to the master
proc dts_streaming_debug {base name probes} {
    set    ret ""
    set    size [expr 64*$probes]
    append ret "$name {"
    append ret "compatible = \"netcope,streaming_debug_master\";"
    append ret "reg = <$base $size>;"
    append ret "probes = <$probes>;"
    append ret "version = <0x00010000>;"
    append ret "};"
    return $ret
}
