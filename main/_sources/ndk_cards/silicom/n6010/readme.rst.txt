.. _card_n6010:

Silicom N6010
-------------

- Card information:
    - Vendor: Silicom
    - Name: N6010
    - Ethernet ports: 2x QSFP
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.silicom-usa.com/pr/4g-5g-products/4g-5g-adapters/fpga-smartnic-n6010-intel-based/>`_
- FPGA specification:
    - FPGA part number: ``AGFB014R24A2E2V``
    - Ethernet Hard IP: E-Tile (up to 100G Ethernet)
    - PCIe Hard IP: P-Tile (up to PCIe Gen4 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`E-Tile in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`P-Tile in the PCIe Module <ndk_intel_pcie_mod>`
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 100g2`` command for firmware with 2x100GE (default).
    - Use ``make 25g8`` command for firmware with 8x25GE.
    - Use ``make 10g8`` command for firmware with 8x10GE.
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES, starting with the nfb-framework version 6.18.0.

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro and PACSign tool installed, including a valid license.
