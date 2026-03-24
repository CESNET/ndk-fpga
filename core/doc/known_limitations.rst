.. _known_limitations:

Known Limitations
=================

Maximal jumbo frames
********************

For DMA Medusa maximal supported frame length (MTU) is 16332 bytes. DMA Calypte supports only frames that have up to 4096 bytes.
For proper MTU functionality for DMA transfers, it may be necessary to set the correct SW buffer sizes, this can be done using the nfb-dma tool.
Don't forget to also properly set the MTU in the Ethernet MAC using the nfb-eth tool, the default value here is 1526 bytes.

DPDK settings
*************

The DPDK native DMA drivers require the ``--iova-mode pa`` setting. This is set by default on most machines, but on some AMD systems
it can cause issues, potentially leading to host system shutdown. The recommended way to run a DPDK application with DPDK native drivers is:

::

  dpdk-testpmd --iova-mode pa -a 0000:17:00.0,queue_driver=native
