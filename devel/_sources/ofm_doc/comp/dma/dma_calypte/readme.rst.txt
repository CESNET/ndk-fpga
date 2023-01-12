.. _dma_calypte:

DMA Calypte
===========

.. vhdl:autoentity:: DMA_CALYPTE

Provided DMA configurations
---------------------------
The design can be configured for various bus widths and PCIe IP core
configurations.

#. Device: AMD/Xilinx Kintex UltraScale+

   PCI Express configuration: Gen3 x8

   Internal bus width: 256 bits

   Frequency: 250 MHz

   Input MFB configuration: 1,4,8,8

   Output MFB configuration: 1,1,8,32

Future expected
^^^^^^^^^^^^^^^

.. WARNING::
   Those configurations are not supported yet.

#. Device: AMD/Xilinx Kintex UltraScale+

   PCI Express configuration: Gen3 x16

   Internal bus width: 512 bits

   Frequency: 250 MHz

   Input MFB configuration: 2,4,8,8

   Output MFB configuration: 2,1,8,32

Subcomponents
-------------

.. toctree::
   :maxdepth: 1

   comp/rx/readme
   comp/tx/readme
