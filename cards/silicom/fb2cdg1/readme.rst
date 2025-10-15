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
    - FPGA part number: ``AGMF039R47A2E2VR0``
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
