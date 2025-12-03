.. _card_fb2cdg1:

Silicom fb2CDg1\@AGM39D-2
-------------------------

- Card information:
    - Vendor: Silicom
    - Name: fb2CDg1\@AGM39D-2 (ThunderFjord)
    - Ethernet ports: 2x QSFPDD56
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.silicom-usa.com/pr/server-adapters/programmable-fpga-server-adapter/fpga-intel-based-2/fpga-intel-agilex-based/fpga-smartnic-fb2cdg1agm39d-2-intel-based/>`_
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
    - See the ``<NDK-FPGA_root_directory>/card/silicom/fb2cdg1/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for Minimal app, may vary for other apps):
    - Use ``make 400g2`` command for firmware with 2x400GE (default).
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES, starting with the nfb-framework version 6.28.5

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro and PACSign tool installed, including a valid license.

Board Variants
^^^^^^^^^^^^^^

This card exists in multiple variants.
The correct variant for the firmware build can be selected using the Makefile parameter BOARD_VARIANT, for example as follows:

.. code::

    $ cd <NDK-FPGA_root_directory>/apps/minimal/build/fb2cdg1
    $ make BOARD_VARIANT=1

**Allowed values of BOARD_VARIANT parameter**

- ``BOARD_VARIANT=1`` - The board uses FPGA part number ``AGMF039R47A1E2VC`` (Production sample).
- ``BOARD_VARIANT=0`` - The board uses FPGA part number ``AGMF039R47A2E2VR0`` (Engineering sample).

Initial Boot instructions
^^^^^^^^^^^^^^^^^^^^^^^^^
The card itself should be preloaded with firmware designed by Silicom.
This design can be used to load an FPGA image to the BMC flash via PCIe using the Silicom ``rawcardtool`` tool.

**Execute the following steps to perform the manual initialization:**

    1. Obtain PCIe address of the card by the command below. In this example, the PCIe address is ``01:00.0`` and will be used in the next steps:

        .. code::

            $ lspci | grep "Silicom Denmark Device"
            01:00.0 Ethernet controller: Silicom Denmark Device 0001
    2. Ensure the card respond to memory space accesses by command:

        .. code::

            $ setpci -s 01:00.0 COMMAND=0x0002
    3. Flash the ``fpga_page1_pacsign_user1.bin`` file to the card using RawCardTool provided by Silicom:

        .. code::

            $ rawcardtool_fjord --device 01:00.0 --flash fpga_page1_pacsign_user1.bin
    4. Set your design as default by command:

        .. code::

            $ rawcardtool_fjord --device 01:00.0 --fpgadefault user1
    5. Boot your design executing:

        .. code::

            $ rawcardtool_fjord --device 01:00.0 --reboot-fpga user1

.. note::

    The ``fpga_page1_pacsign_user1.bin`` file will be located in the build folder of your application after building. For NDK-FPGA, the folder is ``ndk-fpga/apps/minimal/build/fb2cdg1``.

.. note::

    If some bars are unmapped, power cycle the server.

If the ``rawcardtool`` tool is unavailable, it is possible to use JTAG to load the design (SOF file), and ``nfb-boot`` command to load the BMC flash with the FPGA image:

    .. code::

        $ nfb-boot -f0 fb2cdg1-minimal-pcie1xgen5x8x8-400g2.nfw
