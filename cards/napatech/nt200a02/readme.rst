.. _card_napatech_nt200a02:

Napatech NT200A02
--------------

- Card information:
    - Vendor: Napatech
    - Name: NT200A02
    - Ethernet ports: 2x QSFP28
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.napatech.com/products/nt200a02-smartnic-capture>`_
- FPGA specification:
    - FPGA part number: ``xcvu5p-flva2104-2L-e``
    - Ethernet Hard IP: CMAC (100G Ethernet)
    - PCIe Hard IP: USP

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`CMAC in the Network Module <ndk_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`USP in the PCIe Module <ndk_pcie_mod>`
    - See the ``<NDK-FPGA_root_directory>/card/napatech/nt200a02/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for Minimal app, may vary for other apps):
    - Use ``make 100g2`` command for firmware with 2x100GbE (default).
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES, starting with the nfb-framework version 6.26.4.
        - .. warning:: It is neccessary to reboot the OS after changing or rebooting the FW using nfb-boot, otherwise the FLASH memory will not be detected by the driver. See "nfb-boot information" below for details.
    - OR use JTAG (see "JTAG programming" below).

JTAG programming
^^^^^^^^^^^^^^^^^^^^^^

1. Buld the firmware using ``make`` as described above ("Generate bitstream" using Vivado GUI flow)
2. Connect USB cable to the JTAG interface of the card
3. Open Hardware manager in Vivado
4. Program the device

For more information, refer to the `Programming and debugging manual <https://docs.xilinx.com/r/2022.2-English/ug908-vivado-programming-debugging/Opening-the-Hardware-Manager?tocId=x0two8P7pmYkinePAp~Scg>`_
of the Vivado

.. note::
    To build the NDK firmware for this card, you must have the Xilinx Vivado installed, including a valid license.

nfb-boot information
^^^^^^^^^^^^^^^^^^^^

Currently, the `nfb-boot` functionality is limited to one firmware change per OS boot (PCIe reset). More precisely, the FLASH memory becomes unavailable to the driver upon the first FPGA reset initiated by the `nfb-boot` tool (internally performed by the ICAP primitive).

It is possible to repeatedly access/write the firmware slot using `nfb-boot -w0` until `nfb-boot -F0` is executed. Then, it is still possible to repeatedly reboot the FW stored in the slot (`nfb-boot -F0`), but the OS must be rebooted in order to write the FW slot again.

This limitation stems from the "PCI-RESET driven image switching" mechanism implemented by the BMC. The FLASH memory QSPI interface is duplicated to two QSPI interfaces on the FPGA:

1. The "native" QSPI interface used during the power-on FPGA configuration.
2. The ISP (In-System update Programming) interface, which is routed to general-purpose FPGA pins.

The BMC controls a switch, which activates one of these two interfaces.
On card power-on (or cold reset), the native interface is activated so that the FPGA can load the FW from the FLASH memory. After that, the ISP interface is selected. The FLASH memory is now accessible to the FPGA through the ISP interface and this is the interface utilized by the `nfb-boot` tool. However, when the BMC detects a JTAG programming cable or when the FPGA is reset using the ICAP primitive, the FLASH interface is again switched to the native one (the FLASH memory can be written with Vivado HW Manager). That is why it is no longer possible to read or write the FLASH using the `nfb-boot`, but rebooting the FW (`nfb-boot -F0`) still works as it uses the native interface. The next OS reboot triggers a PCIe reset, which allows the BMC to "recover" and the ISP interface is activated again.
