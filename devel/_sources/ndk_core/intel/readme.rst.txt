.. _ndk_arch:
.. _ndk_intel:

NDK architecture
================

The Network Development Kit (NDK) is available for the selected card based on FPGA. The NDK allows users to quickly and easily develop new network appliances based on FPGA acceleration cards. The NDK is optimized for high throughput and scalable to support 10, 100 and 400 Gigabit Ethernet.

.. image:: doc/img/card_with_ndk.drawio.svg
    :align: center
    :width: 100 %

The diagram above shows a simplified NDK architecture on a generic FPGA board.
The NDK top level architecture consists of several building blocks:

- MI bus interconnection (MI Splitter,...) allows access to Control and Status Register (CSR)
- The Network module provides transmission and reception of Ethernet packets to/from the network.
- The DMA module controls the high-speed packet data transfer to the memory of the host PC.
- The PCIe module mediates the communication via the PCIe interface for the DMA module and MI transactions. It also contains a ROM with a description of the loaded firmware.
- The Application is a space in the NDK firmware dedicated to the user application. It can receive and transmit data through the Network and DMA modules, and can also access external memory.
- Time Stamp Unit (TSU) is used to generate accurate time stamps for Network module and Application core
- The Memory controller provides data transfer between the external memory and the FPGA
- The FPGA controller allows access to the QSPI flash memory and request a reboot of the FPGA

.. note::

    Some blocks can be connected more than once in the NDK platform. For example, it is a Network module if the target card contains multiple Ethernet ports (QSFP slots) or a PCIe module if the used card allows connecting more than one PCIe connector.

.. toctree::
   :maxdepth: 2
   :hidden:

   doc/app
   doc/mi
   doc/eth
   doc/dma
   doc/pcie
   doc/mem
   doc/tsu
