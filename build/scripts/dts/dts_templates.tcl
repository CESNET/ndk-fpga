# dts_templates.tcl: templates for various node types within the DeviceTree
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Vladisav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Adds a string property to a Device Tree node
# 1. DTS   - a reference to Device Tree string
# 2. name  - name of a string property
# 3. value - value of a string property
proc dts_appendprop_string {DTS name value} {
    upvar 1 $DTS dts
    append dts "$name = \"$value\";\n"
}

# Adds integer property to a Device Tree node
# 1. DTS   - a reference to Device Tree string
# 2. name  - name of an integer property
# 3. value - value of a integer property
proc dts_appendprop_int {DTS name value} {
    upvar 1 $DTS dts
    append dts "$name = <$value>;\n"
}

# Adds register as a "reg" property to a Device Tree node
# 1. DTS  - a reference to Device Tree string
# 2. addr - base address of a register
# 3. size - size of a register
proc dts_appendprop_reg {DTS addr size} {
    upvar 1 $DTS dts
    append dts "reg = <$addr $size>;\n"
}

# Adds cells that specify processing of address and size values within reg properties of a DT node
# 1. DTS  - a reference to Device Tree string
# 2. addr - specifies how many cells within the reg property represent the BASE ADDRESS of a register
# 3. size - specifies how many cells within the reg property represent the SIZE of a register
# NOTE: A cell within a reg property is a value of type uint32.
proc dts_add_cells {DTS {addr 1} {size 1}} {
    upvar 1 $DTS dts
    dts_appendprop_int dts "#address-cells" $addr
    dts_appendprop_int dts "#size-cells" $size
}

# Adds the minimal set of properties (compatble string and a register address)
# 1. DTS        - a reference to DTS
# 2. base_addr  - base address in the MI address space
# 3. size       - size of the register space in the MI address space
# 4. compatible - compatible string
proc dts_appendprop_comp_node {DTS base_addr size compatible} {
    upvar 1 $DTS dts

    dts_appendprop_string dts "compatible" "$compatible"
    dts_appendprop_reg dts $base_addr $size
}

# This creates a node within a DTS
# 1. DTS   - a reference to Device Tree string
# 2. alias - (also called label) provides an alternative name used for cross-referencing within a
#            Device Tree
# 3. name  - a name of a node
# 4. body  - a set of procedures that add properties to a node (see example within the documentation
#            of a Build System)
proc dts_create_labeled_node {DTS alias name body} {
    upvar 1 $DTS dts

    if {$alias ne ""} {
        append dts "$alias: "
    }
    append dts "$name {\n"
    uplevel 1 $body
    append dts "};\n"
}

# Wrapper over dts_create_labeled_node that creates a node without a label
proc dts_create_node {DTS name body} {
    uplevel 1 [list dts_create_labeled_node $DTS "" $name $body]
}

# Create default mi node
proc dts_create_default_mi_node {DTS INDEX body} {
    append mi_body [subst {
        dts_add_cells $DTS
        dts_appendprop_string $DTS "compatible" "netcope,bus,mi"
        dts_appendprop_string $DTS "resource" "PCI$INDEX,BAR0"
        dts_appendprop_int $DTS "width" "0x20"
    }] $body
    uplevel 1 [list dts_create_labeled_node $DTS "mi${INDEX}" "mi_bus${INDEX}" "$mi_body"]
}
