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

**How to run Memory Tester:**

- The RPM package ``python3-nfb`` is required and you can obtain it from the `@CESNET/nfb-framework COPR repository <https://copr.fedorainfracloud.org/coprs/g/CESNET/nfb-framework/>`_.
- Install ``data_logger`` python package from source code using the following commands...
- ``cd <NDK-APP-XXX_root_directory>/ndk/ofm/comp/debug/data_logger/sw``
- ``python3 setup.py install --user``
- Then go to the mem tester tool directory...
- ``cd <NDK-APP-XXX_root_directory>/ndk/ofm/comp/debug/mem_tester/sw``
- Then external memory test can be run using the ``python3 mem_tester.py`` command.

**Example output of Memory Tester:**

.. code-block::

    $ python3 mem_tester.py
    || ------------------- ||
    || TEST WAS SUCCESSFUL ||
    || ------------------- ||

    Mem_logger statistics:
    ----------------------
    write requests       33554431        
      write words        134217724       
    read requests        33554431        
      requested words    134217724       
      received words     134217724       
    Flow:
      write               160.78 [Gb/s]
      read                161.68 [Gb/s]
      total               161.23 [Gb/s]
    Time:
      write               427.42 [ms]
      read                425.04 [ms]
      total               852.46 [ms]
    Latency:
      min                 96.00 [ns]
      max                 555.00 [ns]
      avg                 131.56 [ns]
      histogram [ns]:
        93.4 - 117.5 ... 12613618        
        117.5 - 141.6 ... 13893635        
        141.6 - 165.7 ... 6618217         
        503.0 - 527.1 ... 74899           
        527.1 - 551.2 ... 265549          
        551.2 - 575.3 ... 88513           
    Errors:
      zero burst count   0               
      simultaneous r+w   0               
    Paralel reads count:
      min                0               
      max                13              
      avg                 10.83 
        0.0 -   4.0 ... 4               
        4.0 -   8.0 ... 27238           
        8.0 -  12.0 ... 4294967295      
        12.0 -  16.0 ... 13345442        

.. note::

    See the :ref:`Memory Tester <mem_tester>` module documentation for a more detailed description.

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
