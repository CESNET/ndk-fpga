.. _known_limitations:

Known Limitations
=================

Maximal jumbo frames
********************

The maximum supported frame length (MTU) for DMA Medusa is 16,332 bytes. DMA Calypte supports frames up to 4,096 bytes only.
For proper MTU functionality during DMA transfers, you may need to configure the software buffer sizes using the ``nfb-dma`` tool.
Also configure the MTU in the Ethernet MAC using the ``nfb-eth`` tool; the default value is 1,526 bytes.

DPDK settings
*************

The DPDK native DMA drivers require the ``--iova-mode pa`` setting. This is set by default on most machines, but on some AMD systems
it can cause issues, potentially leading to host system shutdown. The recommended way to run a DPDK application with DPDK native drivers is:

::

  dpdk-testpmd --iova-mode pa -a 0000:17:00.0,queue_driver=native
