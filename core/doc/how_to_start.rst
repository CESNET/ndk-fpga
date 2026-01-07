.. _ndk_how_to_start:

How to start
************

This chapter describes steps for building the FPGA firmware, loading it into the FPGA card, and using it.

What dependencies are needed to build an FPGA firmware
======================================================

- The NDK build system is for Linux operating systems only. We recommend using any RHEL-compatible OS, for example, Rocky Linux 8+.
- The dtc/libfdt package is required. On RHEL-compatible OS, you can use the following command: ``sudo dnf install dtc``.
- To build the FPGA firmware, you must have Intel Quartus Prime Pro or Xilinx Vivado (depending on the target card) installed, including a valid license.
- You can always find information about the required version of the synthesis tools (Quartus/Vivado) in the ``<NDK-FPGA_root_directory>/README.md`` file.

How to build an FPGA firmware with an NDK-based application
===========================================================

- Go to the ``<NDK-FPGA_root_directory>/apps/minimal/build/<your_card>/`` directory.
- Check or modify the ``app_conf.tcl`` file, where you can change the firmware configuration.
- Build the FPGA firmware with Quartus/Vivado by the ``make`` command in the same folder.
- If you do not have a DMA Medusa IP (it is not part of the open-source NDK), you must use open-source DMA Calypte IP using the command ``make DMA_TYPE=4``.
- Wait until the FPGA firmware build successfully finishes.
- The FPGA firmware file (bitstream) is in the same directory in the NDK format (.nfw) or the Quartus/Vivado format (.sof/.bit).

List of make parameters:
------------------------

.. envvar:: PCIE_CONF

   Allows to set the PCIe configuration, for example: ``make PCIE_CONF=1xGen4x16``. More information can be found in the :ref:`documentation of the PCIe module <ndk_pcie_mod>`.

.. envvar:: DMA_TYPE

   Allows to select the DMA controller, for example ``make DMA_TYPE=4``. More information and allowed values can be found in the :ref:`documentation of the DMA module <ndk_dma>`.

.. _BOARD_VARIANT:

.. envvar:: BOARD_VARIANT

   Allows setting the board variant number for correct firmware settings. This parameter is not available for all FPGA cards. You can find the allowed values in the NDK documentation for the specific card (for example, Bittware IA-440i). Alternatively, you may also encounter a similar parameter: ``BOARD_REV``.


How to prepare the FPGA card and the host PC
============================================

- The target FPGA card may require proper switch settings. Check the card manufacturer's instructions.
- Plug the target FPGA card into the PCIe slot of the host PC.
- Install `the NDK drivers and tools <https://github.com/CESNET/ndk-sw>`_ on the host PC. The RPM packages are available in `the NDK Copr repository <https://copr.fedorainfracloud.org/coprs/g/CESNET/nfb-framework/>`_. Alternatively, `the pre-built .rpm and .deb packages can be found here <https://github.com/CESNET/ndk-sw/releases>`_.

.. WARNING::
    The FPGA card and its firmware are designed for a specific PCIe generation and a specific number of PCIe lines. If you plug an FPGA card into a slot that does not support such PCIe configuration, you may experience slower data transfer over the PCIe interface or a general malfunction.

How to load the firmware to an FPGA card
========================================

The NDK platform uses the `nfb-boot tool <https://cesnet.github.io/ndk-sw/tools/nfb-boot.html>`_ to load the new firmware into the FPGA (booting). You can find an example of how to use it to load firmware into an FPGA card below.

.. WARNING::
    The nfb-boot tool expects that some NDK firmware is already loaded in the FPGA. If this is not your case, follow the FPGA card manufacturer's instructions for loading the FPGA firmware.

.. NOTE::
    The method of booting the FPGA firmware may vary from card to card;  the nfb-boot tool does not support all cards. Please refer to your card's documentation for more detailed information. For example, :ref:`the firmware can be uploaded to the Intel Stratix 10 DX FPGA Development Kit using Quartus and prepared scripts <card_s10dx_dk>`.

- Copy the ``your_ndk_firmware.nfw`` file into the host PC with your connected card (if it is not already there).
- Boot the NDK firmware by using the ``nfb-boot -f0 your_ndk_firmware.nfw`` command.
- Wait until the NDK firmware boot successfully finishes.

How to check the NDK firmware in the FPGA
=========================================

The NDK platform uses the `nfb-info tool <https://cesnet.github.io/ndk-sw/tools/nfb-info.html>`_ to read the basic information about the NDK firmware from the FPGA card. Using this tool, we can check that our NDK firmware has booted correctly. An example of the output of the nfb-info tool can be seen below:

.. code-block:: text

    $ nfb-info
    --------------------------------------- Board info ----
    Board name                 : COMBO-GENERIC
    Serial number              : 0
    Network interfaces         : 1
    ------------------------------------ Firmware info ----
    Card name                  : IA-440I-VAR1
    Project name               : NDK_MINIMAL
    Project variant            : 400G1
    Project version            : 0.11.0
    Built at                   : 2025-08-15 12:14:10
    Build tool                 : Quartus Version 25.1.0 Build 129 03/26/2025 SC Pro Edition
    Build author               : cabal@cesnet.cz
    Build revision             : 7ba87361
    RX queues                  : 32
    TX queues                  : 32
    ETH channels               : 1
    -------------------------------------- System info ----
    PCIe Endpoint 0:
    * PCI slot                : 0000:05:00.0
    * PCI link speed          : 32 GT/s
    * PCI link width          : x16
    * NUMA node               : 0
    * MI BAR 0 size           : 64 MiB
    * MI BAR 2 size           : 16 MiB

Further work with the NDK
=========================

After you have completed the first steps with the NDK firmware, you may want to learn more about the NDK architecture or start testing the NDK firmware.
The following references provide the information to do just that.

- :ref:`Here, you can read about frequently used terms in NDK firmware <ndk_terminology>`.
- :ref:`Here, you can find detailed information about the NDK firmware architecture <ndk_arch>`.
- :ref:`Here, you can find detailed information about the NDK configuration files and parameters <ndk_configuration>`.
- :ref:`Here, you can learn how to test R/W requests to the registers in the NDK firmware or what other tests are available and how to utilize them <ndk_testing>`.
