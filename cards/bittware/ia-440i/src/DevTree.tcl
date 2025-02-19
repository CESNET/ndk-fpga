# DevTree.tcl: Component DeviceTree file
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

proc dts_card_specific {base} {
    set ret ""

    append ret "boot_controller {"
    append ret "compatible = \"bittware,bmc\";"
    append ret "reg = <$base 0x44>;"
    append ret "version = <0x00000003>;"
    append ret "};"
    return $ret
}
