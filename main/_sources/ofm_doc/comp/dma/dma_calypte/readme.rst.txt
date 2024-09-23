.. _dma_calypte:

DMA Calypte
===========

This core provides simple DMA functionality for both RX and TX directions.
The design was primary focused on the lowest latency possible for the
transaction from the input of the DMA core to reach its output. The block scheme
as well as its connection to the NDK design is provided in the following figure:

.. figure:: img/tx_calypte_block-dma_whole_block.svg
    :align: center
    :width: 1000px

.. vhdl:autoentity:: DMA_CALYPTE

Supported PCIe Configurations
-----------------------------

The design can be configured for various bus widths and PCIe IP core
configurations.

#. Device: AMD Kintex UltraScale+

   PCI Express configuration: **Gen3 x8**

   Internal bus width: 256 bits

   Frequency: 250 MHz

   Input MFB configuration: 1,4,8,8

   Output MFB configuration: 1,1,8,32


#. Device: AMD Kintex UltraScale+, Intel Agilex F

   PCI Express configuration: **Gen3 x16 (AMD), Gen4 x16 (Intel)**

   Internal bus width: 512 bits

   Frequency: 250 MHz (AMD), 400 MHz (Intel)

   Input MFB configuration: 1,8,8,8

   Output MFB configuration: 2,1,8,32

Local Subcomponents
-------------------

.. toctree::
   :maxdepth: 1

   comp/rx/readme
   comp/tx/readme
