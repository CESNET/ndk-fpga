# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>
#            Martin Spinler <spinler@cesnet.cz>

import fdt


def create_dtb_simple(comp_name: str, comp_base: int, comp_size: int, compatible_str: str, bus_name: str = "mi0"):
    """Creates a Device Tree represented as binary blob.

    Args:
        addr: Max 32-bit integer to write to the address register.
        comp_name: Component name.
        comp_base: Component's base address.
        comp_size: Component's address space size.
        compatible_str: Component' compatible string.
        bus_name: Name of the bus the component connects to.

    Returns:
        Binary blob representation of the Device Tree.
    """

    myfdt = fdt.FDT()

    mycomp = fdt.Node(comp_name)
    mycomp.set_property("reg", [comp_base, comp_size])
    mycomp.set_property("compatible", compatible_str)

    mybus = fdt.Node(bus_name)
    mybus.set_property("compatible", "netcope,bus,mi")
    mybus.append(mycomp)

    myfdt.add_item(mybus)
    return myfdt.to_dtb(version=17)
