.. _card_alveo_u200:

AMD Alveo U200
--------------

- Card information:
    - Vendor: AMD/Xilinx
    - Name: Alveo U200
    - Ethernet ports: 2x QSFP28
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.xilinx.com/products/boards-and-kits/alveo/u200.html>`_
- FPGA specification:
    - FPGA part number: ``xcu200-fsgd2104-2-e`` (basically same as VU9P)
    - Ethernet Hard IP: CMAC (100G Ethernet)
    - PCIe Hard IP: USP (up to PCIe Gen3 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`CMAC in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`USP in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-APP_root_directory>/ndk/card/alveo-u200/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 100g2`` command for firmware with 2x100GbE (default).
    - Use ``make 100g0`` command for firmware with CMAC disabled but DMAs and Application core remaining (experimental feature).
- Support for booting the NDK firmware using the nfb-boot tool:
    - NO, use JTAG (see below).

Programming the device
^^^^^^^^^^^^^^^^^^^^^^

1. Buld the firmware using ``make`` as described above ("Generate bitstream" using Vivado GUI flow)
2. Connect USB cable to the JTAG interface of the card
3. Open Hardware manager in Vivado (build on 2022.2)
4. Program the device

For more information, refer to the `Programming and debugging manual <https://docs.xilinx.com/r/2022.2-English/ug908-vivado-programming-debugging/Opening-the-Hardware-Manager?tocId=x0two8P7pmYkinePAp~Scg>`_
of the Vivado

.. note::
    To build the NDK firmware for this card, you must have the Xilinx Vivado installed, including a valid license.

.. warning::
   Ethernet interface has not been properly tested on this device, although CMACs can be included.
