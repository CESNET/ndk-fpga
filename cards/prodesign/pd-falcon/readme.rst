
PRO DESIGN Falcon
---------------------------

- Card Information:
    - Vendor: PRO DESIGN 
    - Name: PRO DESIGN Falcon (PD-FALCON-1SM21BEU2F55E2VG-DS-AP-PCIE-150)
    - Ethernet Ports: 4x QSFP-DD
    - PCIe Connectors: 1x
    - `FPGA Card Website <https://www.prodesign-fpga-acceleration.com/products/prodesign-falcon-stratix-10/>`_
    - The FPGA Card User Guide is only available with the card itself.
- FPGA Specification:
    - FPGA Part Number: ``1SM21BEU2F55E2VG``
    - Ethernet Hard IP: E-Tile (supports up to 100G Ethernet)
    - PCIe Hard IP: H-Tile (supports up to PCIe Gen3 x16)

NDK Firmware Support
^^^^^^^^^^^^^^^^^^^^

- Supported Ethernet Cores in the NDK Firmware:
    - :ref:`E-Tile in the Network Module <ndk_intel_net_mod>`
- Supported PCIe Cores in the NDK Firmware:
    - H-Tile is supported.
    - Refer to the ``<NDK-APP_root_directory>/ndk/cards/prodesign/pd-falcon/config/card_conf.tcl`` file for supported PCIe configurations.
- Makefile Targets for Building NDK Firmware (for NDK-APP-Minimal, may vary for other applications):
    - Use the ``make 100g2`` command to build firmware with 2x100GE (default).
- Support for Booting NDK Firmware Using the nfb-boot Tool:
    - Not supported. Refer to the card manual for booting instructions.

.. note::

    To build the NDK firmware for this card, you must have Intel Quartus Prime Pro installed, along with a valid license.

Boot Instructions
^^^^^^^^^^^^^^^^^

- First, build the NDK firmware. Note that the first build will fail—this is expected.
- After the first failed implementation, run the ``<NDK-APP_root_directory>/ndk/cards/prodesign/pd-falcon/src/ip/htile_pcie_fix.sh`` script to fix the generated H-Tile IP core.
- The next build should complete successfully.
- Once the NDK firmware build is complete, a bitstream file will be generated.
- To load the firmware, attach the USB-Blaster II Download Cable via the Edge Debug Board to the card.
- Create an image for the QSPF flash according to the FPGA Card User Guide.
- Load the created image onto the FPGA card following the instructions in the FPGA Card User Guide.
