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
    - FPGA part number: ``AGIB023R18A1E1V``, ``AGIB023R18A1E1VC`` (Differs with)
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

Board Variants
^^^^^^^^^^^^^^

This card exists in multiple variants.
The correct variant for the firmware build can be selected using the Makefile parameter BOARD_VARIANT, for example as follows:

.. code::

    $ cd <NDK-FPGA_root_directory>/apps/minimal/build/ia-860m
    $ make BOARD_VARIANT=3

**Allowed values of BOARD_VARIANT parameter**

- ``BOARD_VARIANT=4`` - The board uses FPGA part number ``AGMF039R47A1E2VC``, and has different pinout for BMC than BV0.
- ``BOARD_VARIANT=3`` - The board uses FPGA part number ``AGMF039R47A2E2VR0``, and has different pinout for BMC than BV0.
- ``BOARD_VARIANT=0`` - The board uses FPGA part number ``AGMF039R47A2E2VR0``.

General boot information
^^^^^^^^^^^^^^^^^^^^^^^^

The BMC on the card doesn't store firmware images on fixed flash offsets. Instead, it uses filesystem-like access.
The offsets can vary, and the software is responsible for positioning and allocating the space for the new image.
This behaviour is adapted for NDK standard approach in ``nfb`` kernel driver like this:

- Slot ID 1 (recovery) is reserved for an (existing) image at flash offset 0.
- Slot ID 0 is reserved for the (existing) image right after Slot ID 1.
- All other images or empty slots are numbered from ID 2.
- The driver creates additional empty image slots between images.
- The slot IDs can be renumbered after any boot action.
- User can set boot priority for each image using the ``nfb-boot -P X,Y,Z``, where X, Y and Z are slot IDs.
  For example, ``nfb-boot -P 4,2`` sets priority 0 for the slot ID 4 and priority 1 for the slot ID 2 (other slot priorities will be untouched).
  The priorities are listed in the square brackets in the output of the ``nfb-boot -l`` command (present just for the supported cards).
  Lower numbers means higher priority (except -1, which is undefined).
  Be aware that the priority numbers must be unique for each image and the empty slots can't have priority.
- The non-empty slot with ID X can be deleted with command ``nfb-boot -D X``.
- The non-empty slots are represented also by image names.
- The non-empty slots can be directly written as usual. If the size of the already present (overwritten) image is insufficient, the driver will also try to consume the empty slot right after the selected slot. If that empty slot does not exist (is not empty), the boot fails.

.. warning::

   The boot priority should be set after writing a firmware, especially to Slot ID 1 (recovery), otherwise no image can be booted after Power-on. For the default NDK behaviour, the priority should be set with ``nfb-boot -P 1,0``

Bootstrap instructions
^^^^^^^^^^^^^^^^^^^^^^

Phase 1: Let the nfb driver handle the device
"""""""""""""""""""""""""""""""""""""""""""""

.. code-block:: bash

    # Generate nfb-boostrap.dtb file; assuming the vendor OEM firmware is booted
    sudo yum install python3-nfb-tools
    nfb-bootstrap -c IA-860M

    # Find PCI address for device
    PCI_BFN=$(lspci -d 12ba: -D | head -n1 | cut -d ' ' -f1)

    # Inject DTB to the driver and load the PCI device to the driver too
    sudo modprobe nfb
    sudo nfb-boot -d $PCI_BFN -I nfb-bootstrap.dtb

    # Set this device as default in current terminal for next commands
    $(nfb-info -q dd -d /dev/nfb/by-pci-slot/$PCI_BFN)

Phase 2: Flash custom image and check for boot
""""""""""""""""""""""""""""""""""""""""""""""

.. code-block:: bash

    # check for original firmware slot (should be ID 1, the ID 0 may be present)
    # check for empty slot (should be nr. 2)
    nfb-boot -l

    # If you do not have the USB cable for the card, stay safe:
    # use an empty slot (probably with ID 2) or a non-empty slot with ID 0,
    # and do not overwrite original (ID 1) firmware yet, in case of failure
    nfb-boot -w 0 myfirmware.nfw
    nfb-boot -F 0

    # The firmware should be now uploaded and live.
    # The nfb-info reads device tree just from the PCI configuration space.
    # But if the machine, for example, cannot assign a PCI BAR resource,
    # the MI access to the BMC fails and the slot list will be empty.
    # The machine warm reboot should fix that (beware, cold reboot loads original firmware)
    nfb-info
    nfb-boot -l

    # If everything is OK, set the new firmware as the second priority (after the original):
    nfb-boot -P 1,0

Phase 3: Replace the original firmware
""""""""""""""""""""""""""""""""""""""

.. code-block:: bash

    # Enable write access to the recovery image (Slot ID 1)
    sudo rmmod nfb; sudo modprobe nfb flash_recovery_ro=0

    # Replace OEM firmware by the custom firmware
    nfb-boot -w1 myfirmware.nfw
    # Note: if the original image is smaller than the custom firmware,
    # this method will not work due to a space issue.
    # Try to flash the same firmware to the next empty slot (2),
    # modify the image priority sequence to 1,2 and then delete the first custom slot (0).
    # This creates sufficient empty slot for rewriting factory firmware (1) with custom firmware.

    # set again the new firmware the second priority (after original):
    nfb-boot -P 1,0

USB boot instructions
^^^^^^^^^^^^^^^^^^^^^

Before you can work with the card, you will need to install Bittware's SDK and IA-860m Card Support Package (CSP) on your host system.
To be able to do that, you will also need Python 3 (version >= 3.8) present on your system, so be sure to get that first.
Next, proceed with the following steps:

- Download the Bittware SDK and IA-860m CSP installers from the `Bittware Developer Website <https://developer.bittware.com>`_ (version 2024.2).
- Install both downloaded packages by following the instructions in the Bittware SDK and CSP Installation manual (accessible on the same website).
- Connect your IA-860m card to the host using the dedicated USB cable.

Once this is done, you can check the card status by issuing ``bw_card_list -v``.
If everything is OK (card has been found and is available via USB), you can use the ``bw_bmc_fpga_load`` utility to manage designs for your card.

- To get more info about the usage and available subprograms of the ``bw_bmc_fpga_load`` utility, type ``bw_bmc_fpga_load -h``.
- Use ``bw_bmc_fpga_load table`` to list all stored flash images.
- Use ``bw_bmc_fpga_load program <ia-860m_design_name>.rbf <address>`` to write the image into the configuration flash on the given address.
- Use ``bw_bmc_fpga_load default <ia-860m_design_name>.rbf`` to make your design the default boot option.
- Use ``bw_bmc_fpga_load load    <ia-860m_design_name>.rbf`` to configure the fpga with your design from the flash.
- Use ``bw_bmc_fpga_load stream  <ia-860m_design_name>.rbf`` to configure the fpga directly without writing it into the flash.

.. note::

   All designs stored inside the configuration flash (or directly loaded into the fpga) must be built using the same version of Quartus Prime Pro.

.. warning::

   So far, there are features of the nfb framework that are not yet fully supported for this card (e. g. ``nfb-eth -T``).
