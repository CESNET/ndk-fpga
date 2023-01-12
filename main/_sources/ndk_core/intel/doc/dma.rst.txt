.. _ndk_intel_dma:

DMA module
^^^^^^^^^^

The connection of the DMA module is shown in the block diagram below.
The DMA module is parametric and handles different numbers of DMA streams.
One DMA module IP (DMA Medusa) is connected to each stream.
DMA Medusa has an internal architecture divided into several DMA endpoints, each of which is rated for 100 Gbps throughput.
See :ref:`the DMA Medusa documentation <dma_medusa>` for a detailed description.
Individual DMA endpoints are statically mapped to a physical PCIe endpoint (mapping is implemented in :ref:`the PCIe module <ndk_intel_pcie_mod>`).
The current implementation allows one or two DMA endpoints to be mapped to one PCIe endpoint.

.. note::

    The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback.

.. image:: img/dma_module.drawio.svg
    :align: center
    :width: 100 %

DMA Medusa or individual DMA channels are controlled through MI requests, therefore the :ref:`MI bus <mi_bus>` is also mapped to DMA Medusa from individual PCIe endpoints.
The DMA module optionally includes a :ref:`Gen Loop Switch (GLS) module <gls_debug>` for each DMA stream.
The GLS module is used for debugging, contains packet generators and allows to enable loopback modes.
The GLS module can be controlled through MI requests.

**References**

- :ref:`DMA Medusa documentation <dma_medusa>`
- :ref:`GLS module documentation <gls_debug>`
- :ref:`MFB bus specification <mfb_bus>`
- :ref:`MVB bus specification <mvb_bus>`
- :ref:`MI bus specification <mi_bus>`
