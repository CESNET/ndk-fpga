.. _card_s10dx_dk:

Intel Stratix 10 DX FPGA DK
---------------------------

- Card information:
    - Vendor: Intel
    - Name: Stratix 10 DX FPGA Development Kit (DK-DEV-1SDX-P)
    - Ethernet ports: 2x QSFP56
    - PCIe conectors: Edge connector + optional UPI connectors
    - `FPGA Card Website <https://www.intel.com/content/www/us/en/products/details/fpga/development-kits/stratix/10-dx.html>`_
    - `FPGA Card User Guide <https://www.intel.com/content/www/us/en/docs/programmable/683561/current/getting-started.html>`_
    - `FPGA Card Schematic <https://www.intel.com/content/dam/altera-www/global/en_US/support/boards-kits/stratix10/dx_fpga/dx-dev-kit-enpirion-051219-100719.pdf>`_
- FPGA specification:
    - FPGA part number: ``1SD280PT2F55E1VG``
    - Ethernet Hard IP: E-Tile (up to 100G Ethernet)
    - PCIe Hard IP: P-Tile (up to PCIe Gen4 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`E-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`P-Tile in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-APP_root_directory>/ndk/card/dk-dev-1sdx-p/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 100g2`` command for firmware with 2x100GE (default).
    - Use ``make 25g8`` command for firmware with 8x25GE.
    - Use ``make 10g8`` command for firmware with 8x10GE.
- Support for booting the NDK firmware using the nfb-boot tool:
    - NO, see booting instructions bellow.

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro installed, including a valid license.

Boot instructions
^^^^^^^^^^^^^^^^^

- After the NDK firmware build is complete, you will have a bitstream file called ``my_bitstream.sof``.
- Use the ``<NDK-APP_root_directory>/ndk/cards/dk-dev-1sdx-p/scripts/generate_pof.sh my_bitstream.sof`` command to convert the bitstream file to .pof format for flash memory.
- On the host PC where the card is connected, write the .pof bitstream to the flash memory with the command ``<NDK-APP_root_directory>/ndk/cards/dk-dev-1sdx-p/scripts/write_pof.sh my_bitstream.pof``.
- You must power off and on the PC to power cycle it completely. Only then is the new NDK firmware loaded into the FPGA.

.. note::

    This procedure requires the Intel Quartus to be installed and the PC must also be connected to the card using an USB cable (JTAG).
