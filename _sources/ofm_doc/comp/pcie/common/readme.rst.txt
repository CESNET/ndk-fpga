PCI_EXT_CAP
------------

PCI Extended Capability unit stores OFM-specific identification mechanisms.
It is typically connected to the PCIe core and mapped to the PCI configuration space
as a Vendor-Specific Extension Capability (VSEC) with ID 0x0D7B.

.. list-table:: Address space
    :widths: 5 15 5 40
    :header-rows: 1

    * - Offset
      - Name
      - Access
      - Description (dword bits in format 31 downto 0)

    * - 0x00
      - PCIe Extended Capability header
      - RO
      - Next capability Offset & Capability Version & PCI Express Extended Capability ID

    * - 0x04
      - PCIe VSEC header
      - RO
      - VSEC Length & VSEC Rev & VSEC ID (``0x020 & 0x1 & 0x0D7B``)

    * - 0x08
      - Flags
      - RO
      - Endpoint ID flag (1b) & Card ID flag (1b) & Reserved (26b) & Endpoint ID (4b)

    * - 0x0C
      - DTB length
      - RO
      - Real length of DTB in bytes

    * - 0x10
      - DTB address
      - RW
      - Index of DTB data dword

    * - 0x14
      - DTB data
      - RO
      -

    * - 0x18
      - Extra address
      - RO
      - Index of Extra data register

    * - 0x1C
      - Extra data
      - various
      -

.. list-table:: Extra space
    :widths: 5 15 5 40
    :header-rows: 1

    * - Index
      - Name
      - Access
      - Description

    * - 0-3
      - Card ID
      - RO
      - Unique identifier of card in system; up to 128b

Device Tree
~~~~~~~~~~~

The Device Tree with the firmware description is obtained through the `dtb_pkg` VHDL package.

Software gets the length of stored DT in bytes by reading the `DTB length` register
and then performs the appropriate number of reads from the dword-sized `DTB data` register.
Each read is preceded with a write of the requested dword index to the `DTB address` register.

Device Tree is typically stored in the form of Device Tree Blob (`dtb`) compressed by the `xz`.

Endpoint ID
~~~~~~~~~~~

For multi-PCIe endpoint firmware, the software must identify a particular PCIe endpoint.
For that purpose, it reads the `Endpoint ID` value (4b) in the `Flags` register.
The `Endpoint ID` is valid only if the `Endpoint ID flag` bit is set.

Extra space
~~~~~~~~~~~

The `Extra data` register uses indirect addressing like the `DTB data` register.
Access must be preceded with a write of an index to the `Extra address` register.

Card ID
~~~~~~~

When more cards are present in the system, the software needs to pair
all PCIe endpoints of multi-PCIe cards to the correct parent device
(typically based on the primary PCIe endpoint with the `Endpoint ID` value 0).

For successful pairing, the firmware must announce a system-wide unique identifier of the card.
The software then reads the `Card ID` value (128b) in the `Extra data` register
and binds all PCIe endpoints with the same `Card ID` together.

The `Card ID` is valid only if the `Card ID flag` bit is set.
