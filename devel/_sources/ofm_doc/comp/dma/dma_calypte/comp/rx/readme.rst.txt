.. _rx_dma_calypte:

RX DMA Calypte
==============

This is receiving part of the DMA Calypte core. Simple block scheme is provided
in the following figure:

.. figure:: img/rx_dma_calypte_arch.svg
    :align: center
    :scale: 150%

.. vhdl:autoentity:: RX_DMA_CALYPTE

.. toctree::
   :maxdepth: 1
   :caption: Subcomponents

   comp/input_buffer/readme
   comp/trans_buffer/readme
   comp/hdr_insertor/readme
   comp/hdr_manager/readme
   comp/software_manager/readme
