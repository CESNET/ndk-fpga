.. _ndk_app_minimal:

Minimal NDK application
=======================

The NDK-based Minimal application is a simple example of how to build an FPGA application using the NDK. It can also be a starting point for your NDK-based application. The NDK-based Minimal application does not process network packets in any way; it only sends and receives them. If the DMA IP is enabled (see the :ref:`DMA Module chapter <ndk_dma>`), then it forwards the network packets to and from the computer memory.

The top-level application provides the Ethernet, DMA, and :ref:`MI configuration bus <mi_bus>` connections to the individual APP subcore. One independent APP subcore is instantiated for each Ethernet stream. The Ethernet and DMA streams are implemented using the :ref:`MFB buses <mfb_bus>` and the :ref:`MVB buses <mvb_bus>`. The block diagram below shows the connection of the Minimal application.

.. image:: img/app_core.drawio.svg
    :align: center
    :width: 100 %

.. NOTE::
    In case there is just one DMA stream and the number of ETH streams (= number of APP subcores) is more than one, the DMA Streams Merger and DMA Chan Mod modules provide the splitting/merging of the DMA streams and DMA channels for each APP subcore. In this case, the DMA channels available within the single DMA stream are evenly divided between all APP subcores.

In each subcore in the TX direction (DMA to ETH) the DMA channels are statically mapped to Ethernet channels (if there is more than one) according to the MSBs of the DMA channel number. For example, if there are 4 Ethernet channels and 32 DMA channels, the ETH channel number (2 bits) is taken from bits 4 and 3 of the DMA channel number. So packets from DMA channels 0-7 would all be routed to ETH channel 0, packets from DMA channels 8-15 would all be routed to ETH channel 1, etc.

In the RX direction (again, for each subcore), the mapping of Ethernet channels to DMA channels is configurable by the user. The mapping is performed by the :ref:`MVB Channel Router <mvb_channel_router>`. By default, each Ethernet channel has a portion of the available DMA channels to which it can send packets. And in the default state, it sends packets to the available DMA channels in  the round-robin mode.```

The Memory Testers
******************

The NDK-based Minimal application also contains :ref:`Memory Tester <mem_tester>` modules connected to external memory controllers. These modules make it easy to test the operation of external memories and measure their properties (throughput, latency). The Avalon-MM bus is used to access the external memory, see `Avalon Interface Specifications <https://www.intel.com/content/www/us/en/docs/programmable/683091/>`_.

The source code for the Memory Tester control tool is available in the ``<NDK-APP-XXX_root_directory>/ndk/ofm/comp/debug/mem_tester/sw`` folder.

- First, the source code must be compiled using the ``make`` command.
- Then all external memory tests can be run using the ``./mem_tester -t all`` command.
- You can also run tests with the Python helper script and generate a PDF report with the test results: ``python3 report_gen.py``.

The example of MI offsets
*************************

This example assumes that the Minimal application consists of two subcores and also contains two Memory tester modules.

.. code-block::

    0x0000000-0x07FFFFF -- APP subcore 0 (registers of DMA channel distribution + reserved space)
    0x0800000-0x0FFFFFF -- APP subcore 1 (registers of DMA channel distribution + reserved space)
    0x1000000-0x17FFFFF -- Memory Tester 0
    0x1800000-0x1FFFFFF -- Memory Tester 1

.. note::

    The final MI address is obtained by summing the base address and the offset. If the base address of the application core is ``0x02000000``, then the final address of APP subcore 1 will be ``0x02000000 + 0x0800000 = 0x02800000``.
