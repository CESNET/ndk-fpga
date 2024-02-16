.. _ndk_app:

The Application
===============
The NDK is designed for creating new network applications for packet processing in a deep pipeline. The NDK provides space for your application and defines several interfaces for communication with devices on the network, with software (control and data), or with external memory. We refer to this space in the NDK as **the Application**.

Depending on the selected FPGA card, there are several ETH streams for communication over an Ethernet network and several DMA streams for communication with the host CPU through the DMA module. There are also several `Avalon-MM interfaces <https://www.intel.com/content/www/us/en/docs/programmable/683091/22-3/introduction-to-memory-mapped-interfaces.html>`_ for access to external memory (typically DDR4) and an MI interface for access to the CSR implemented in the application. ETH and DMA streams use a combination of MFB (for packet data) and MVB (for packet headers and metadata) buses to transfer Ethernet packets. The Application allows you to assign the selected user clock to individual parts of the design. A typical connection of the Application is shown in the block diagram below:

.. image:: img/ndk_app.drawio.svg
    :align: center
    :width: 100 %

We recommend splitting the Application into several parts that we call Application cores. Typically, an Application core is instantiated for each Ethernet stream. Depending on the selected FPGA card, the number of ETH streams is equal to the number of DMA streams, or there are multiple ETH streams and only one DMA stream. For such cases, the NDK has prepared modules (see the `Application implementation in NDK-APP-Minimal <https://github.com/CESNET/ndk-app-minimal/blob/main/app/intel/application_core.vhd>`_) to ensure that each Application Core is correctly connected to the available DMA interfaces. They also ensure proper distribution of the available DMA channels among the Application cores.

How to use the Application interfaces
*************************************

The following sections describe how to work with each of the Application interfaces. You will also learn in which formats you can receive data and in which you must send it. We also strongly recommend that you read the :ref:`MFB bus specification <mfb_bus>`, :ref:`MVB bus specification <mvb_bus>` and :ref:`MI bus specification <mi_bus>`. The MTU of packets transferred via DMA or Ethernet can be set using configuration parameters, see :ref:`chapter "Configuration files and parameters" <ndk_configuration>`. The set MTU values are then available in the :ref:`DeviceTree <ndk_devtree>` description of the NDK firmware.

Receiving packets from Ethernet
-------------------------------

Ethernet packets enter the application over two buses (``ETH_RX_*``). The MVB bus carries the packet metadata, and the MFB bus carries the actual packet data. Both buses have independent flow control.

.. WARNING::
    Even though the MVB and MFB buses are independent, data must be transferred over both of them. If they are not, for example, when one bus has the ``*_DST_RDY`` set permanently to 0, a buffer or a FIFO memory will fill up, and the data transfer will get stuck.

The packets are transferred as Ethernet frames without CRC. The ``eth_hdr_pack`` package defines the metadata format. The package is displayed below:

.. vhdl:autopackage:: eth_hdr_pack

Transmitting packets to the Ethernet
------------------------------------

The packets are sent to the Ethernet only through the MFB bus (``ETH_TX_MFB_*``). In this case, the metadata is transferred in a special signal: ``ETH_TX_MFB_HDR``. This signal is valid for each MFB Region where an Ethernet packet starts. The packet data must contain an Ethernet frame without the CRC, which is calculated and inserted further in the design. The minimum allowed length of the packet data is 60B, if necessary, the application must add padding to the packet. The metadata format is also defined in the ``eth_hdr_pack`` package (see the previous section).

Receiving packets from the DMA module
-------------------------------------

The application receives packets from the DMA module over two buses, MVB and MFB (``DMA_TX_*``). As before, MVB carries the metadata, and MFB carries the actual packet data. Both buses have independent flow control.

.. WARNING::
    Even though the MVB and MFB buses are independent, data must be transferred over both of them. If they are not, for example, when one bus has the ``*_DST_RDY`` set permanently to 0, a buffer or a FIFO memory will fill up, and the data transfer will get stuck.

The MVB metadata bus does not use a single ``MVB_DATA`` signal but  multiple data signals instead:

- ``MVB_LEN`` - the length of the packet in bytes
- ``MVB_HDR_META`` - metadata for the DMA header (see the format below)
- ``MVB_CHANNEL`` - the DMA channel number

The MFB bus transfers the packet data, which may contain a user header before the payload data (e.g., an Ethernet packet). You can determine the presence of the user header and its length from the metadata in the ``DMA_TX_MVB_HDR_META`` signal (see below).

**The format of the metadata for the DMA header (DMA_TX_MVB_HDR_META):**

========= ========== ===========================================
Bit range Item name  Item description
========= ========== ===========================================
0  to 7   HDR_LEN    The size of the user header in bytes. HDR_LEN=0 means that the user header is not present in the packet.
8  to 11  HDR_ID     A 4-bit identification of the type/format of the user header, the definition of each HDR_ID value is application-specific. HDR_ID is referred to as "Packet specific flags" in the `NDP API <https://cesnet.github.io/ndk-sw/libnfb-api-ndp.html>`_.
========= ========== ===========================================

Transmitting packets to the DMA module
--------------------------------------

The application sends packets to the DMA module over two buses, MVB and MFB (``DMA_RX_*``), which have the same roles as stated in previous sections. As before, MVB carries the metadata, and MFB carries the actual packet data. Again, the MVB bus does not use a single ``MVB_DATA`` signal but multiple data signals instead:

- ``MVB_LEN`` - the length of the packet in bytes
- ``MVB_HDR_META`` - metadata for DMA header (see the format in the previous section)
- ``MVB_CHANNEL`` - the DMA channel number
- ``MVB_DISCARD`` - A discard flag (the packet is discarded on the DMA input when you set this flag to 1)

The MFB bus transfers the packet data, which may contain a user header before the payload data (e.g., an Ethernet packet). 
You can determine the presence of the user header and its length from the metadata in the ``DMA_RX_MVB_HDR_META`` signal (see the previous section).
The minimum allowed length of the packet data is 60B, if necessary, the application must add padding to the packet.

.. WARNING::
    The application must also send the corresponding MVB data with each MFB packet, or the data transfer will get stuck.

Read/write access to the Application registers from SW
------------------------------------------------------

The application is typically controlled by a software tool. The NDK provides the `nfb-bus tool <https://cesnet.github.io/ndk-sw/tools/nfb-bus.html#nfb-bus>`_ and an `API for generating read/write memory requests <https://cesnet.github.io/ndk-sw/libnfb-quick-start-registers.html>`_. These are transferred via the :ref:`MI bus <mi_bus>` in the NDK firmware. This memory-oriented bus is wired throughout the NDK firmware, and each part, including the application, has its own allocated address space. You can find more about the MI and the available address space in the :ref:`MI bus interconnect <ndk_mi>` chapter.

The description of the components with a specific address space is implemented in the NDK using a :ref:`DeviceTree <ndk_devtree>`. Also, the Application must have its own DeviceTree description, which can further refer to the internal components and their address spaces. It is a good idea to take inspiration from the `NDK-APP-Minimal application DeviceTree file <https://github.com/CESNET/ndk-app-minimal/blob/main/app/intel/DevTree.tcl>`_ when creating a DeviceTree file for your application.

Ports and generics of the Application
*************************************

In the tables below, you can see a detailed description of the Application interface, i.e., a description of all its generics and ports.

.. vhdl:autoentity:: APPLICATION_CORE
