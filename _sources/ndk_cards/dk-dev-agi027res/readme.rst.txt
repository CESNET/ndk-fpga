.. _card_agi_dk:

Intel Agilex I-Series FPGA DK
-----------------------------

- Card information:
    - Vendor: Intel
    - Name: Agilex I-Series FPGA Development Kit (DK-DEV-AGI027RES)
    - Ethernet ports: 2x QSFP-DD (NDK firmware uses only QSFP-DD 1)
    - PCIe conectors: Edge connector + optional MCIO connectors
    - `FPGA Card Website <https://www.intel.com/content/www/us/en/products/details/fpga/development-kits/agilex/i-series.html>`_
    - `FPGA Card User Guide <https://www.intel.com/content/www/us/en/docs/programmable/683288/current/overview.html>`_
    - `FPGA Card Schematic <https://www.intel.com/content/dam/altera-www/global/en_US/support/boards-kits/agilex/agilex-agi027-devkit-schematic-reva1-apr2021.pdf>`_
- FPGA specification:
    - FPGA part number: ``AGIB027R29A1E2VR0``
    - Ethernet Hard IP: F-Tile (up to 400G Ethernet)
    - PCIe Hard IP: R-Tile (up to PCIe Gen5 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`F-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`R-Tile in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-APP_root_directory>/ndk/card/dk-dev-agi027res/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 400g1`` command for firmware with 1x400GbE (default).
    - Use ``make 200g2`` command for firmware with 2x200GbE.
    - Use ``make 100g4`` command for firmware with 4x100GbE.
    - Use ``make 50g8`` command for firmware with 8x50GbE.
    - Use ``make 40g2`` command for firmware with 2x40GbE.
    - Use ``make 25g8`` command for firmware with 8x25GbE.
    - Use ``make 10g8`` command for firmware with 8x10GbE.
- Support for booting the NDK firmware using the nfb-boot tool:
    - NO, see booting instructions bellow.

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro installed, including a valid license.

Boot instructions
^^^^^^^^^^^^^^^^^

- After the NDK firmware build is complete, you will have a bitstream file called ``my_bitstream.sof``.
- Use the ``<NDK-APP_root_directory>/ndk/cards/dk-dev-agi027res/scripts/generate_pof.sh my_bitstream.sof`` command to convert the bitstream file to .pof format for flash memory.
- On the host PC where the card is connected, write the .pof bitstream to the flash memory with the command ``<NDK-APP_root_directory>/ndk/cards/dk-dev-1sdx-p/scripts/write_pof.sh my_bitstream.pof``.
- You must power off and on the PC to power cycle it completely. Only then is the new NDK firmware loaded into the FPGA.

.. note::

    This procedure requires the Intel Quartus to be installed and the PC must also be connected to the card using an USB cable (JTAG).
