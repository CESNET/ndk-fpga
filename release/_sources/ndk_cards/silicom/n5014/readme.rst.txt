.. _card_n5014:

Silicom N5014
-------------

- Card information:
    - Vendor: Silicom
    - Name: N5014
    - Ethernet ports: 4x QSFP
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.silicom-usa.com/pr/4g-5g-products/4g-5g-adapters/silicom-fpga-smartnic-n5010_series/>`_
- FPGA specification:
    - FPGA part number: ``1SD21BPT2F53E2VG``
    - Ethernet Hard IP: E-Tile (up to 100G Ethernet)
    - PCIe Hard IP: P-Tile (up to PCIe Gen4 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`E-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`P-Tile in the PCIe Module <ndk_intel_pcie_mod>`
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 100g4`` command for firmware with 4x100GE (default).
- Support for booting the NDK firmware using the nfb-boot tool:
    - Yes, starting with the nfb-framework version 6.25.0.

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro and PACSign tool installed, including a valid license.
