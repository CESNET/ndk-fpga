.. _card_s10dx_dk:

Stratix 10 DX FPGA Development Kit
----------------------------------

Stratix 10 DX FPGA Development Kit (DK-DEV-1SDX-P) by Intel was originally used in our team for testing DMA transfers via PCIe (up to 400 Gbps). Then we ported our whole NDK to this card as well. Here is some important information about this card:

- Intel Stratix 10 DX FPGA - 1SD280PT2F55E1VG (1x E-Tile, 4x P-Tile)
- `Development Kit Website <https://www.intel.com/content/www/us/en/programmable/products/boards_and_kits/dev-kits/altera/kit-s10-dx.html>`_
- `Development Kit User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/ug/ug-s10-dx-fpga-dev-kit.pdf>`_
- `Development Kit Schematic <https://www.intel.com/content/dam/altera-www/global/en_US/support/boards-kits/stratix10/dx_fpga/dx-dev-kit-enpirion-051219-100719.pdf>`_

Build instructions
^^^^^^^^^^^^^^^^^^

- Go to ``build/dk-dev-1sdx-p/`` folder in application repository.
- Check or modify ``user_const.tcl`` file, where you can change the firmware configuration.
- Run firmware build in Quartus by ``make`` command.
    - Use ``make 100g2`` command for firmware with 2x100GE (default).
    - Use ``make 25g8`` command for firmware with 8x25GE.
    - Use ``make 10g8`` command for firmware with 8x10GE.
- After the build is complete, you will find bitstream ``my_bitstream.sof`` in the same folder.
- Use the ``../../ndk/cards/dk-dev-1sdx-p/scripts/generate_pof.sh my_bitstream.sof`` command to convert the bitstream file to .pof format for flash memory.
- On the server where the card is connected, write the new bitstream to the flash memory with the command ``../../ndk/cards/dk-dev-1sdx-p/scripts/write_pof.sh my_bitstream.pof``.
- You must power off the server and power it on to completely power cycle and load new firmware.

.. note::

    To build firmware, you must have Quartus Prime Pro installed, including a valid license.

Ethernet Interfaces
^^^^^^^^^^^^^^^^^^^

This card has two QSFP slots (ports). Each is connected to the FPGA via 4 high-speed serial lines supporting up to 25 Gbps (alternatively, two lines with a speed of up to 56 Gbps are supported, but it is not used here). Both QSFP slots are connected to an E-Tile that supports Ethernet Hard IP with the following speeds: ``1x100GE, 4x25GE, 4x10GE``. E-Tile Hard IPs are instanced in Network Module, which providing Ethernet communication to Application core. The architecture of the Network Module :ref:`is described here <ndk_intel_net_mod>`.

PCIe Interfaces
^^^^^^^^^^^^^^^

This card has one PCIe Gen4 x16 edge connector. An additional PCIe connector can be added to the UPI interface using an expansion cable (used for 400G DMA demo only). The FPGA used contains 3x P-Tile, each of which contains PCIe Gen4 x16 Hard IP. In our firmware we use P-Tile in PCIe Gen4 x8+x8 (bifurcation) mode. This setting has worked best for us in terms of DMA transfer performance. P-Tile Hard IPs are instanced in PCIe Module, which providing PCIe communication for DMA module and MI bus (CSR registers). The architecture of the PCIe Module :ref:`is described here <ndk_intel_pcie_mod>`.

.. note::

    The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback.
