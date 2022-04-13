.. _ndk_intel_app:

Application core
^^^^^^^^^^^^^^^^

NDK is designed for creating new network applications processing packets in a deep pipeline. The application core is a space that provides all the necessary resources for such an application.
Depending on the selected card, there are several streams for receiving and sending Ethernet packets, several streams for sending a packet to the host CPU through the DMA module.
There are also several Avalon-MM interfaces for accessing external memory (typically DDR4) and the MI interface (see :ref:`MI bus specification <mi_bus>`) for accessing the CSR implemented in the application.
Ethernet and DMA streams use a combination of MFB (for packet data) and MVB (for packet headers and metadata) buses to transmit packets. See MFB specification and MVB specification.
The application core allows you to assign the selected user clock to individual parts of the design.

.. note::

    The number of streams should match the number of Ethernet ports on the selected FPGA card.

.. note::

    The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback

**Ports and generics of Application core**

In the tables below you can see a detailed description of the application core interface, ie a description of all generics and ports.

.. vhdl:autoentity:: APPLICATION_CORE

**References**

- :ref:`MI bus specification <mi_bus>`
- :ref:`MFB bus specification <mfb_bus>`
- :ref:`MVB bus specification <mvb_bus>`
- `Avalon Interface Specifications (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/manual/mnl_avalon_spec.pdf>`_
