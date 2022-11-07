.. _card_fb4cgg3:

Silicom fb4CGg3\@VU9P
---------------------

- Card information:
    - Vendor: Silicom
    - Name: fb4CGg3\@VU9P also in variant fb2CGg3\@VU9P
    - Ethernet ports: 4x QSFP28 (fb4CGg3) or 2x QSFP28 (fb2CGg3)
    - PCIe conectors: Edge connector
    - `FPGA Card Website <https://www.silicom-usa.com/pr/server-adapters/programmable-fpga-server-adapter/fpga-xilinx-based-2/fb4cgg3vu-100-gigabit-xilinx-virtex-ultrascale/>`_
- FPGA specification:
    - FPGA part number: ``xcvu9p-flgb2104-2-i``
    - Ethernet Hard IP: CMAC (100G Ethernet)
    - PCIe Hard IP: USP (up to PCIe Gen3 x16)

NDK firmware support
^^^^^^^^^^^^^^^^^^^^

- Ethernet cores that are supported in the NDK firmware:
    - :ref:`CMAC in the Network Module <ndk_intel_net_mod>`
- PCIe cores that are supported in the NDK firmware:
    - :ref:`USP in the PCIe Module <ndk_intel_pcie_mod>`
    - See the ``<NDK-APP_root_directory>/ndk/card/fb4cgg3/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile targets for building the NDK firmware (valid for NDK-APP-Minimal, may vary for other apps):
    - Use ``make 100g2`` command for firmware with 2x100GbE for fb2CGg3 card only (default).
    - Use ``make 100g4`` command for firmware with 4x100GbE for fb4CGg3 card only.
- Support for booting the NDK firmware using the nfb-boot tool:
    - YES.

.. note::

    To build the NDK firmware for this card, you must have the Xilinx Vivado installed, including a valid license.
