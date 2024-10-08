# DevTree.tcl: Component DeviceTree file
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# 1. base - base address on MI bus
# 2. type - type of card 
proc dts_boot_controller {base type} {
    set    ret ""
    
    append ret "boot_controller {"
    append ret "compatible = \"netcope,boot_controller\";"
    append ret "reg = <$base 8>;"
    append ret "version = <0x00000001>;"
    append ret "type = <$type>;"
    if {$type == 1 || $type == 3 } {
        append ret "axi_quad_flash_controller {"
        append ret "reg = <[expr $base+0x100] 0x80>;"
        append ret "compatible = \"xlnx,axi-quad-spi\";"
        append ret "};"
    }
    append ret "};"
    return $ret
}


