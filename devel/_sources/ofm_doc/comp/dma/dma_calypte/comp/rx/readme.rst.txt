.. _rx_dma_calypte:

RX DMA Calypte
==============

This is receiving part of the DMA Calypte core. Simple block scheme is provided
in the following figure:

.. figure:: img/rx_dma_calypte_arch.svg
    :align: center
    :scale: 150%

.. vhdl:autoentity:: RX_DMA_CALYPTE


Subcomponents
-------------

.. toctree::
   :maxdepth: 1
   :caption: Subcomponents

   comp/input_buffer/readme
   comp/trans_buffer/readme
   comp/hdr_insertor/readme
   comp/hdr_manager/readme
   comp/software_manager/readme

----------------
UVM Verification
----------------

.. figure:: img/uvm_ver.jpg
    :align: center
    :scale: 60%


Verification Plan
-----------------

TODO:


Coverage Mesure
---------------

There is three test in Multiver script. High percentage of uncovered lines is due to unreacheable states and due to mi comunication with software manager. Mi comunication is tested by hw tests.

.. list-table:: test configuration
   :widths: 50 50 50 50 50 50
   :header-rows: 1

   * - conf name
     - Regions
     - Max packet size
     - buffer addres width
     - input fifo (RX)
     - channels num

   * - default
     - 1(~40Gb/s)
     - 2^16-1
     - 16-bit
     - NONE
     - 2

   * - 32_channel
     - 1(~40Gb/s)
     - 2^16-1
     - 16-bit
     - NONE
     - 32

   * - 32_channel
     - 1(~40Gb/s)
     - 2^16-1
     - 16-bit
     - On input
     - 2

.. list-table:: coverage
   :widths: 50 50 50 50
   :header-rows: 1

   * - conf name
     - base
     - full speed
     - merge

   * - default
     - 63.1942%
     - 63.4521%
     - 64.0038%

   * - 32_channels
     - 62.6153%
     - 61.4392%
     - 62.7494%

   * - opt_fifo_en
     - 65.3934%
     - 64.9822%
     - 65.9905%

Delay is mesure only for full spead test. Which allweys accept output from DUT. Delay represents how many nanoseconds take to go through DMA Calypte.

.. list-table:: delay
   :widths: 50 50 50 50 50
   :header-rows: 1

   * - conf name
     - min
     - max
     - average
     - standard deviation

   * - default
     - 53ns
     - 68ns
     - 57ns
     - 5ns

   * - 32_channels
     - 40ns
     - 1752ns
     - 56ns
     - 63ns

   * - opt_fifo_en
     - 44ns
     - 428ns
     - 294ns
     - 158ns

