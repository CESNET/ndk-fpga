.. _card_fb2cghh:

Silicom fb2CGhh\@KU15P
----------------------

- Card information:
    - Vendor: Silicom
    - Name: fb2CGhh\@KU15P
    - Ethernet ports: 2x QSFP28
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.silicom-usa.com/pr/server-adapters/programmable-fpga-server-adapter/fpga-xilinx-based-2/fb2cghhku15p-fpga-card/>`_
- FPGA specification:
    - FPGA part number: ``xcku15p-ffve1760-2-e``
    - Ethernet Hard IP: CMAC (100G Ethernet)
    - PCIe Hard IP: USP (up to PCIe Gen3 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`CMAC in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`USP in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-APP_root_directory>/ndk/card/fb2cghh/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 100g2`` command for firmware with 2x100GbE (default).
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES.

.. note::

    To build the NDK firmware for this card, you must have the Xilinx Vivado installed, including a valid license.
