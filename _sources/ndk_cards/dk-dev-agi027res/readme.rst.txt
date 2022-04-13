.. _card_agi_dk:

Agilex I-Series FPGA Development Kit
------------------------------------

Agilex I-Series FPGA Development Kit (DK-DEV-AGI027RES) by Intel is supported in the NDK only with the primary goal of accelerating the debugging of the 400G NDK design for :ref:`the XpressSX AGI-FH400G card <card_400g1>`. Here is some important information about this card:

- Intel Agilex I-Series FPGA - AGIB027R29A1E2VR0 (1x F-Tile, 3x R-Tile)
- `Development Kit Website <https://www.intel.com/content/www/us/en/products/details/fpga/development-kits/agilex/i-series.html>`_
- `Development Kit User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/ug/ug-agilex-i-fpga-devl-kit.pdf>`_
- `Development Kit Schematic <https://www.intel.com/content/dam/altera-www/global/en_US/support/boards-kits/agilex/agilex-agi027-devkit-schematic-reva1-apr2021.pdf>`_

Build instructions
^^^^^^^^^^^^^^^^^^

- Go to ``build/dk-dev-agi027res/`` folder in application repository.
- Check or modify ``user_const.tcl`` file, where you can change the firmware configuration.
- Run firmware build in Quartus by ``make`` command.
    - Use ``make 400g1`` command for firmware with 1x400GbE (default).
    - Use ``make 200g2`` command for firmware with 2x200GbE.
    - Use ``make 100g4`` command for firmware with 4x100GbE.
    - Use ``make 50g8`` command for firmware with 8x50GbE.
    - Use ``make 40g2`` command for firmware with 2x40GbE.
    - Use ``make 25g8`` command for firmware with 8x25GbE.
    - Use ``make 10g8`` command for firmware with 8x10GbE.
- After the build is complete, you will find bitstream ``my_bitstream.sof`` in the same folder.
- Use the ``../../ndk/cards/dk-dev-agi027res/scripts/generate_pof.sh my_bitstream.sof`` command to convert the bitstream file to .pof format for flash memory.
- On the server where the card is connected, write the new bitstream to the flash memory with the command ``../../ndk/cards/dk-dev-agi027res/scripts/write_pof.sh my_bitstream.pof``.
- You must power off the server and power it on to completely power cycle and load new firmware.

.. note::

    To build firmware, you must have Quartus Prime Pro installed, including a valid license.

Ethernet Interface
^^^^^^^^^^^^^^^^^^

This card has two QSFP-DD cage (ports). However, our NDK design uses only one QSFP-DD port (QSFP-DD 1). It is connected to the FPGA via 8 high-speed serial lines supporting up to 56 Gbps (FGT). QSFP-DD cage is connected to an F-Tile that contains Ethernet Hard IP supporting the following speeds: ``1x400GbE, 2x200GbE, 4x100GbE, 8x50GbE, 2x40GbE, 8x25GbE, 8x10GbE``. F-Tile Hard IPs are instantiated in Network Module, which provides Ethernet communication to and from the Application core. The architecture of the Network Module :ref:`is described here <ndk_intel_net_mod>`.

.. note::

    Not all Ethernet Hard IP configurations are already available or tested in NDK.

PCIe Interface
^^^^^^^^^^^^^^

This card has single PCIe Gen5 x16 edge connector (R-tile - 14C) and MCIO Connector (R-tile - 15C) which can be used to implement another PCIe interface with 16 lines. In our NDK design uses both R-Tile interfaces to implement 400 Gbps DMA solution (1x PCIe Gen5 x16/x8+x8 or 2x PCIe Gen4 x16/x8+x8). R-Tile Hard IPs are instantiated in PCIe Module, which provides PCIe communication to and from the Application core. The architecture of the PCIe Module :ref:`is described here <ndk_intel_pcie_mod>`.

.. note::

    The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback.
