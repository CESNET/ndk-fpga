.. _card_terasic-a2700:

Terasic A2700
----------------

- Card information:
    - Vendor: Terasic
    - Name: Mercury A2700 Accelerator Card
    - Ethernet ports: 2x QSFP-DD
        - 400G
        - up to 200G (200/100/40/25/10) - Unsupported
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.terasic.com.tw/cgi-bin/page/archive.pl?Language=English&CategoryNo=142&No=1300&PartNo=1#contents>`_
- FPGA specification:
    - FPGA part number: ``AGIB027R29A1E2VB``
    - Ethernet Hard IP: F-Tile (up to 400G Ethernet)
    - PCIe Hard IP: R-Tile (up to PCIe Gen5 x16)
    - Four DDR4 SO-DIMM Socket
        - One shared with HPS

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`F-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`R-Tile in the PCIe Module <ndk_intel_pcie_mod>`
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 400g1`` command for firmware with 1x400GE (default).
- Support for booting the NDK firmware using the nfb-boot tool:
    - TODO

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro installed, including a valid license.
    Design requires enabled bifurcation (x8x8) on target machine

Boot instructions (initial)
^^^^^^^^^^^^^^^^^^^^^^^^^^^
Supported boot is handled by the Secure Device Manager (SDM), which has its own 1Gb flash to store Factory and User defined image.
To enable this method, it is necessary to set the switches on the board as follows:
- Ensure that the MSEL[2:0] switch on the board is set to 'Active Serial Normal' mode - MSEL[2:0] = 3'b011
    - Set SW4 to 2'b01 and SW5 to 2'b10.
    - The SW4(1) set to 0 to load user image or to 1 to load factory image after power up.
- For more detailed description refer to `Mercury A2700 User Manual <https://www.terasic.com.tw/cgi-bin/page/archive_download.pl?Language=English&No=1300&FID=96d539627a1f37a9b6386bd0571f7e3f>`_

Before you can use the nfb-boot tool, you must write the initial NDK firmware to flash memory using a regular JTAG programmer.
It is possible to use Micro-USB port marked as 'USB/UART' on the Terasic card for this purpose.

- Build your application calling ``make`` in the build folder with 'Makefile'.
- After the NDK firmware build is complete, you will have a bitstream file called ``my_bitstream.sof``.
- Use the ``NDK-APP_root_directory/ndk_fpga/cards/terasic/a2700/scripts/generate_jic.sh my_bitstream.sof my_bitstream.sof`` command to convert the two bitstream files to .jic format for flash memory.
    - This creates a flash image and sets address spaces in the flash to hold the factory and user images.
- On the host PC where the card is connected, write the .jic bitstream to the flash memory with the command ``<NDK-APP_root_directory/ndk_fpga/cards/terasic/a2700/scripts/write_jic.sh my_bitstream.jic``.
    - You must power off and on the PC to power cycle it completely. Only then is the new NDK firmware loaded into the FPGA. (Do not simply reboot, otherwise the factory design will still be loaded on the FPGA.)

Check that the procedure was successful by running ``nfb-boot -l``. This command should list the recovery and application slots in the boot flash.
Reboot/New Configuration of the FPGA is performed by calling ``nfb-boot -F0`` or ``nfb-boot -F1``.
Loading new design to the boot flash is performed by calling ``nfb-boot -f0 your_design.nfw``. (This may take up to 30 minutes)

.. note::

    - Make sure SW2 (next to the power connector) is set to 'ON' position
        - In the 'ON' position, the switch is switched to the connector (It is not by default)
    - This procedure requires the Intel Quartus to be installed and the PC must also be connected to the card using an USB cable (JTAG).
    - Loading the .jic bitstream into the flash can take up to 30 minutes.
