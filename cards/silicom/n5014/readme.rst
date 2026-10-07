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

HBM
^^^

The FPGA contains two HBM2 stacks (top and bottom). The NDK firmware connects each stack
through one HBM IP instance with 16 AXI ports, one port per pseudo-channel.

- Number of HBM ports is set by ``HBM_PORTS`` in ``card_conf.tcl`` (or overridden in ``app_conf.tcl``):
    - ``0``: HBM disabled (card default).
    - ``16``: top stack only.
    - ``32``: both stacks (NDK-APP-Minimal default).
- AXI interface of each port:
    - Data width: 256 bits.
    - Address width: 28 bits, i.e. 256 MB per port; each port has its own address space (8 GB in total with 32 ports).
    - Burst: pseudo-BL8, one burst transfers 64 bytes (two 256-bit words).
- Ordering: the HBM controller has the re-order buffer (ROB) enabled, so read responses
  come back in the AXI order even when the controller serves the requests out of order.
  Issuing reads with a unique AXI ID per transaction lets the controller reorder them, which
  greatly increases the read performance (see the table below).
- Clocks:
    - User (AXI) clock: 300 MHz, the ``clk_usr_x3`` clock from FPGA_COMMON (``MISC_OUT(4)``).
    - HBM memory clock: 800 MHz.
- Reset: each stack has its own ``HBM_RESET`` controller. After the first successful calibration with a locked user clock, it resets the HBM controller once more and waits until the calibration succeeds again.
- Theoretical throughput with 32 ports: 32 x 300 MHz x 256 b = 2457.6 Gbps in each direction (read and write have separate AXI channels).

Measured HBM performance
~~~~~~~~~~~~~~~~~~~~~~~~

Measured with the HBM tester on all 32 ports (NDK-APP-Minimal, 300 MHz, September 2026).
Percentages are relative to the theoretical maximum of one direction (2457.6 Gbps).

==================  ============  ======================  ==========================
Test                Addressing    One AXI ID for all      New AXI ID per transaction
==================  ============  ======================  ==========================
Read only           sequential    1088 Gbps (44.3 %)      2376 Gbps (96.7 %)
Read only           random        499 Gbps (20.3 %)       2274 Gbps (92.5 %)
Write only          sequential    2349 Gbps (95.6 %)      2350 Gbps (95.6 %)
Write only          random        2326 Gbps (94.7 %)      2326 Gbps (94.7 %)
==================  ============  ======================  ==========================

.. note::

    To build the NDK firmware for this card, you must have the Intel Quartus Prime Pro and PACSign tool installed, including a valid license.
