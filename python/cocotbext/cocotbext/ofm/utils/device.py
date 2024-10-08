import fdt


def get_dtb(comp_name: str, comp_base: int, comp_offset: int, compatible_str: str, bus_name: str, version: int = 17):
    """Creates a Device Tree represented as binary blob.

    Args:
        addr: Max 32-bit integer to write to the address register.
        comp_name: Component name.
        comp_base: Component's base address.
        comp_offset: Component's address offset (size of its address space).
        compatible_str: Component' compatible string.
        bus_name: Name of the bus the component connects to.
        version: Version of the to_dtb function.

    Returns:
        Binary blob representation of the Device Tree.

    """

    myfdt = fdt.FDT()

    mycomp = fdt.Node(comp_name)
    mycomp.set_property("reg", [comp_base, comp_offset])
    mycomp.set_property("compatible", compatible_str)

    mybus = fdt.Node(bus_name)
    mybus.set_property("compatible", "netcope,bus,mi")
    mybus.append(mycomp)

    myfdt.add_item(mybus)
    return myfdt.to_dtb(version=version)
