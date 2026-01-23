.. _card_ia-440i:

Bittware IA-440I
----------------

- Card information:
    - Vendor: Bittware
    - Name: IA-440I
    - Ethernet ports: 1x QSFP-DD
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.bittware.com/fpga/ia-440i/>`_
- FPGA specification:
    - FPGA part number: ``AGIB023R18A1E1V``, ``AGIB023R18A1E1VC``
    - Ethernet Hard IP: F-Tile (up to 400G Ethernet)
    - PCIe Hard IP: R-Tile (up to PCIe Gen5 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`F-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`R-Tile in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-FPGA_root_directory>/cards/bittware/ia-440i/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 400g1`` command for firmware with 1x400GE (default).
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES, starting with the nfb-framework version 6.26.0.

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro installed, including a valid license.

Detailed boot information can be found in the :doc:`../bmc_3.x`

:ref:`Board Variants <BOARD_VARIANT>`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- ``BOARD_VARIANT=1`` - The board uses FPGA part number ``AGIB023R18A1E1VC`` (C0 F-Tile).
- ``BOARD_VARIANT=0`` - The board uses FPGA part number ``AGIB023R18A1E1V``.
