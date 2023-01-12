.. _ndk_app_minimal:

Minimal NDK application
^^^^^^^^^^^^^^^^^^^^^^^

The Minimal application serves as a simple demonstration of how to build an FPGA application using the NDK. It can also be used as a starting point for building your own application. The Minimal application does not process network packets in any way, it can only receive and send them. If the DMA module IP is enabled, the network packets are forwarded to the computer memory.

.. warning::

    The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback. `You can get NDK including DMA Module IP and professional support through our partner BrnoLogic <https://support.brnologic.com/>`_.

.. image:: img/app_core.drawio.svg
    :align: center
    :width: 100 %

The block diagram above shows the connection of the Minimal application core, which is available in this repository.
This core supports multiple Ethernet and DMA streams, each of which is independent and contains logic (subcore) that transfers packets between the Ethernet and DMA interfaces in both directions.
In the direction from ETH to DMA, configurable packet distribution to DMA channels is supported. Packet distribution on DMA channels is performed by component :ref:`MVB Channel Router <mvb_channel_router>`. By default, a portion of the DMA channels is allocated for each ETH channel, to which packets are distributed in round robin mode. In the opposite direction (from DMA to ETH), DMA channels are statically mapped to available ETH channels. The ETH channel number is determined by the high bits of the DMA channel number.
The application core also contains :ref:`Memory Tester modules <mem_tester>` connected to external memory controllers.
These modules make it easy to test the operation of external memories and measure their properties (throughput, latency).

**Example of MI space offsets for the Minimal application**

This example assumes that the Minimal application consists of two subcores and also contains two Memory tester modules.

.. code-block::

    0x0000000-0x07FFFFF -- APP subcore 0 (registers of DMA channel distribution + reserved space)
    0x0800000-0x0FFFFFF -- APP subcore 1 (registers of DMA channel distribution + reserved space)
    0x1000000-0x17FFFFF -- Memory Tester 0
    0x1800000-0x1FFFFFF -- Memory Tester 1

.. note::

    The final MI address is obtained by summing the base address and the offset. If the base address of the application core is ``0x02000000``, then the final address of APP subcore 1 will be ``0x02000000 + 0x0800000 = 0x02800000``.

**References**

- :ref:`MI bus specification <mi_bus>`
- :ref:`MFB bus specification <mfb_bus>`
- :ref:`MVB bus specification <mvb_bus>`
- `Avalon Interface Specifications (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/manual/mnl_avalon_spec.pdf>`_
- :ref:`Memory Tester module documentation <mem_tester>` 
