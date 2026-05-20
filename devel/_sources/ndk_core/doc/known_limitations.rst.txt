.. _known_limitations:

Known Limitations
=================

Maximal jumbo frames
********************

The Ethernet MAC supports a maximum MTU of 16,383 bytes on all Ethernet types. However, the DMA Medusa engine cannot always transfer
frames of the full MAC MTU. The maximum frame length supported by DMA RX depends on the size of the user DMA header (:ref:`hdr_meta_format`),
which is prepended to the Ethernet packet and becomes part of the transferred data:

| **max Ethernet frame (RX)** = 16,383 − ``HDR_LEN``
| **max DMA frame size (RX)** = 16,379 − ``HDR_LEN``

where ``HDR_LEN`` is the user header size in bytes. For example:

- **MINIMAL** application (``HDR_LEN`` = 0): max Ethernet frame = 16,383, max
  DMA frame = 16,379 (= MAC MTU − 4 B CRC).
- **NIC** application (``HDR_LEN`` = 4): max Ethernet frame = 16,379, max
  DMA frame = 16,375.

Exceeding the DMA limit causes an internal counter overflow — the DMA reports an incorrect byte count (approximately 2\ :sup:`32` minus
the actual length) or stalls completely. NDP applications may also show incorrect speed for frames near the limit.

In the TX direction, DMA Medusa supports up to 16,383 bytes (the frame is sent with +4B CRC = 16,387 B on the wire).

DMA Calypte supports frames up to 4,096 bytes only.

For proper MTU functionality during DMA transfers, you may need to configure the software buffer sizes using the ``nfb-dma`` tool.
Also configure the MTU in the Ethernet MAC using the ``nfb-eth`` tool; the default value is 1,526 bytes.

DPDK settings
*************

The DPDK native DMA drivers require the ``--iova-mode pa`` setting. This is set by default on most machines, but on some AMD systems
it can cause issues, potentially leading to host system shutdown. The recommended way to run a DPDK application with DPDK native drivers is:

::

  dpdk-testpmd --iova-mode pa -a 0000:17:00.0,queue_driver=native
