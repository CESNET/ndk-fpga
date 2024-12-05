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
    - FPGA part number: ``AGIB023R18A1E1V``
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
    - NO.

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro installed, including a valid license.

Boot instructions
^^^^^^^^^^^^^^^^^

Before you can work with the card, you will need to install Bittware's SDK and IA-440i Card Support Package (CSP) on your host system.
To be able to do that, you will also need Python 3 (version >= 3.8) present on your system, so be sure to get that first.
Next, proceed with the following steps:

- Download the Bittware SDK and IA-440i CSP installers from the `Bittware Developer Website <https://developer.bittware.com>`_ (version 2024.2).
- Install both downloaded packages by following the instructions in the Bittware SDK and CSP Installation manual (accessible on the same website).
- Connect your IA-440i card to the host using the dedicated USB cable.

Once this is done, you can check the card status by issuing ``bw_card_list -v``.
If everything is OK (card has been found and is available via USB), you can use the ``bw_bmc_fpga_load`` utility to manage designs for your card.

- To get more info about the usage and available subprograms of the ``bw_bmc_fpga_load`` utility, type ``bw_bmc_fpga_load -h``.
- Use ``bw_bmc_fpga_load table`` to list all stored flash images.
- Use ``bw_bmc_fpga_load program <ia-440i_design_name>.rbf <address>`` to write the image into the configuration flash on the given address.
- Use ``bw_bmc_fpga_load default <ia-440i_design_name>.rbf`` to make your design the default boot option.
- Use ``bw_bmc_fpga_load load    <ia-440i_design_name>.rbf`` to configure the fpga with your design from the flash.
- Use ``bw_bmc_fpga_load stream  <ia-440i_design_name>.rbf`` to configure the fpga directly without writing it into the flash.

.. note::

   All designs stored inside the configuration flash (or directly loaded into the fpga) must be built using the same version of Quartus Prime Pro.

.. warning::

   So far, there are features of the nfb framework that are not yet fully supported for this card (e. g. ``nfb-eth -T`` or ``nfb-boot``).
