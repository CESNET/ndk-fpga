.. _card_ia-860m:

Bittware IA-860m
----------------

- Card information:
    - Vendor: Bittware
    - Name: IA-860m
    - Ethernet ports: 3x QSFP-DD (Only 2x used in minimal design)
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.bittware.com/fpga/ia-860m/>`_
- FPGA specification:
    - FPGA part number: ``AGMF039R47A2E2VR0``, ``AGMF039R47A1E2VC``
    - Ethernet Hard IP: F-Tile (up to 400G Ethernet)
    - PCIe Hard IP: R-Tile (up to PCIe Gen5 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`F-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`R-Tile in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-FPGA_root_directory>/cards/bittware/ia-860m/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 400g2`` command for firmware with 2x400GE (default).
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro installed, including a valid license.

Detailed boot information can be found in the :doc:`../bmc_3.x`

:ref:`Board Variants <BOARD_VARIANT>`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The NDK firmware supports different hardware revisions of the IA-860m card, distinguished by the ``BOARD_VARIANT`` parameter.

- ``BOARD_VARIANT=4`` - The board uses FPGA part number ``AGMF039R47A1E2VC``. This variant uses a **different** pinout for BMC communication than variants 0, 1, and 2.
- ``BOARD_VARIANT=3`` - The board uses FPGA part number ``AGMF039R47A2E2VR0``. This variant uses a **different** pinout for BMC communication than variants 0, 1, and 2.
- ``BOARD_VARIANT=0, 1, 2`` - The board uses FPGA part number ``AGMF039R47A2E2VR0``.
    - These variants share the original pinout for BMC communication.
    - Variants 1 and 2 represent updated PCB revisions, but are functionally identical to Variant 0 from the NDK firmware perspective.
