.. _card_ia-420f:

Bittware IA-420F
----------------

- Card information:
    - Vendor: Bittware
    - Name: IA-420F
    - Ethernet ports: 1x QSFP-DD
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.bittware.com/fpga/ia-420f/>`_
- FPGA specification:
    - FPGA part number: ``AGFB014R24B2E2V``
    - Ethernet Hard IP: E-Tile (up to 100G Ethernet)
    - PCIe Hard IP: P-Tile (up to PCIe Gen4 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`E-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`P-Tile in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-APP_root_directory>/ndk/card/ia-420f/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 100g2`` command for firmware with 2x100GE (default).
    - Use ``make 25g8`` command for firmware with 8x25GE.
    - Use ``make 10g8`` command for firmware with 8x10GE.
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES, starting with the nfb-framework version 6.17.1.

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro installed, including a valid license.

Boot instructions (initial)
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Before you can use the nfb-boot tool, you must write the initial NDK firmware to flash memory using a regular JTAG programmer.

- After the NDK firmware build is complete, you will have a bitstream file called ``my_bitstream.sof``.
- Use the ``<NDK-APP_root_directory>/ndk/cards/ia-420f/scripts/generate_jic.sh my_bitstream.sof my_bitstream.sof`` command to convert the two bitstream files to .jic format for flash memory.
- On the host PC where the card is connected, write the .jic bitstream to the flash memory with the command ``<NDK-APP_root_directory>/ndk/cards/ia-420f/scripts/write_jic.sh my_bitstream.jic``.
- You must power off and on the PC to power cycle it completely. Only then is the new NDK firmware loaded into the FPGA.

.. note::

    This procedure requires the Intel Quartus to be installed and the PC must also be connected to the card using an USB cable (JTAG).
