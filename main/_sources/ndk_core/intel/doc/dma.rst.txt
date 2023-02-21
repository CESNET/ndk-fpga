.. _ndk_dma:
.. _ndk_intel_dma:

The DMA module
==============

The DMA module is a wrapper containing the DMA controller (DMA IP), auxiliary, and debug logic. The connection of the DMA module is shown in the block diagram below. The DMA module is parametric and handles different numbers of DMA streams. The number of DMA streams corresponds to the number of instantiated DMA controllers. The currently supported DMA controllers in NDK are:

- **DMA Medusa IP** -- Closed-source DMA controller optimized for high throughput (up to 400 Gbps) and support for multiple PCIe endpoints. See the :ref:`DMA Medusa IP documentation <dma_medusa>` for a detailed description.
- **DMA Calypte IP** -- Open-source DMA controller optimized for low latency communication and supports only one PCIe endpoint. DMA Calypte IP is still under development and not yet ready for use! See the :ref:`DMA Calypte IP documentation <dma_calypte>` for a detailed description.

.. note::

    The DMA Medusa IP is not part of the open-source NDK. `You can get the NDK, including the DMA Medusa IP and professional support, through our partner BrnoLogic. <https://support.brnologic.com/>`_

Each DMA stream consists of two buses: the :ref:`MFB bus <mfb_bus>` is used to transfer data packets, the :ref:`MVB bus <mvb_bus>` is used to transfer DMA instructions to each packet. How a user application should properly use these buses is described in :ref:`The Application chapter <ndk_app>`.

The DMA module optionally includes a :ref:`Gen Loop Switch (GLS) module <gls_debug>` for each DMA stream. The GLS module is used for debugging, contains packet generators and allows to enable loopback modes. The GLS module can be controlled through MI requests.

.. image:: img/dma_module.drawio.svg
    :align: center
    :width: 100 %

Selecting a DMA controller
**************************

Before running the FPGA firmware compilation, the desired DMA controller can be selected using the makefile parameter ``DMA_TYPE``. Without this parameter, the default DMA controller is automatically selected. These are the allowed values:

- ``DMA_TYPE=0`` -- No DMA IP is instantiated. DMA IP is replaced by a loopback.
- ``DMA_TYPE=3`` -- DMA Medusa IP (default DMA controller)
- ``DMA_TYPE=4`` -- DMA Calypte IP

DMA Medusa IP notes
*******************

The DMA Medusa IP has an internal architecture divided into several DMA endpoints, each rated for 100 Gbps throughput. See the :ref:`DMA Medusa documentation <dma_medusa>` for a detailed description. Individual DMA endpoints are statically mapped to a physical PCIe endpoint (mapping is implemented in the :ref:`PCIe module <ndk_pcie_mod>`). The current implementation allows one or two DMA endpoints to be mapped to one PCIe endpoint. Individual DMA channels of the DMA Medusa IP are controlled through MI requests, therefore, the :ref:`MI bus <mi_bus>` is also mapped to the DMA Medusa from individual PCIe endpoints.
