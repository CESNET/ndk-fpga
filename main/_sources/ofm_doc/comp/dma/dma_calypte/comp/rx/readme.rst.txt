.. _rx_dma_calypte:

RX DMA Calypte
==============

This is receiving part of the DMA Calypte core. Simple block scheme is provided
in the following figure:

.. figure:: img/rx_dma_calypte_arch.svg
    :align: center
    :width: 1000px

.. vhdl:autoentity:: RX_DMA_CALYPTE

Control/Status Registers
------------------------

In order for the controller to be controlled by the software, an address space
with configuration/status (C/S) registers is initialized. Currently, each
channel contains its own set of registers with the overall size of 128 B. The
1st channel's registers are located on the address *0x00*, the second on *0x80*, the
third on *0x100*, etc. The registers are connected through :ref:`MI bus <mi_bus>` to
the global configuration tree. The set of C/S for one channel is listed in
the following table.

.. list-table:: Tab. 1
    :align: center
    :widths: auto
    :header-rows: 1

    * - Address
      - Name
      - Access permission (FPGA/Host)
      - Description
    * - 0x00
      - Control
      - R/W
      - Bit 0: Set to 1 to request the enable of a channel. Set to 0 to request stop of a channel.
    * - 0x04
      - Status
      - W/R
      - Bit 0: Set to 1 if a channel is enabled. Set to 0 if the channel is disabled.
    * - 0x08
      - -Reserved-
      - N/A
      - \-
    * - 0x0C
      - -Reserved-
      - N/A
      - \-
    * - 0x10
      - Software data pointer (SDP)
      - R/W
      - Writing pointer for data (up to 16 bits)
    * - 0x14
      - Software header pointer (SDP)
      - R/W
      - Writing pointer for headers (up to 16 bits)
    * - 0x18
      - Hardware data pointer (HDP)
      - W/R
      - Reading pointer for data (up to 16 bits)
    * - 0x1C
      - Hardware header pointer (HHP)
      - W/R
      - Reading pointer for headers (up to 16 bits)
    * - 0x20
      - -Reserved-
      - N/A
      - \-
    * - 0x24
      - -Reserved-
      - N/A
      - \-
    * - 0x28
      - -Reserved-
      - N/A
      - \-
    * - 0x2C
      - -Reserved-
      - N/A
      - \-
    * - 0x30
      - -Reserved-
      - N/A
      - \-
    * - 0x34
      - -Reserved-
      - N/A
      - \-
    * - 0x38
      - -Reserved-
      - N/A
      - \-
    * - 0x3C
      - -Reserved-
      - N/A
      - \-
    * - 0x40
      - Data baseL
      - R/W
      - Base addres of the data buffer in a host memory (lower part).
    * - 0x44
      - Data baseH
      - R/W
      - Base addres of the data buffer in a host memory (upper part).
    * - 0x48
      - Header baseL
      - R/W
      - Base addres of the header buffer in a host memory (lower part).
    * - 0x4C
      - Header baseH
      - R/W
      - Base addres of the header buffer in a host memory (upper part).
    * - 0x50
      - -Reserved-
      - N/A
      - \-
    * - 0x54
      - -Reserved-
      - N/A
      - \-
    * - 0x58
      - Data pointer mask (DPM)
      - R/W
      - Mask for the data pointers (determines data buffer size)
    * - 0x5C
      - Header pointer mask (HPM)
      - R/W
      - Mask for the header pointers (determines header buffer size)
    * - 0x60
      - Received packetsL
      - W/RW (Strobe)
      - Counter of received packets (lower part)
    * - 0x64
      - Received packetsH
      - W/RW (Strobe)
      - Counter of received packets (upper part)
    * - 0x68
      - Received bytesL
      - W/RW (Strobe)
      - Counter of received bytes (lower part)
    * - 0x6C
      - Received bytesH
      - W/RW (Strobe)
      - Counter of received bytes (upper part)
    * - 0x70
      - Discarded packetsL
      - W/RW (Strobe)
      - Counter of discarded packets (lower part)
    * - 0x74
      - Discarded packetsH
      - W/RW (Strobe)
      - Counter of discarded packets (upper part)
    * - 0x78
      - Discarded bytesL
      - W/RW (Strobe)
      - Counter of discarded bytes (lower part)
    * - 0x7C
      - Discarded bytesH
      - W/RW (Strobe)
      - Counter of discarded bytes (upper part)

.. NOTE::
   Some registers have a *strobe* functionality in which case specific
   writes on a counter's address need to be issued from the host in order to
   manipulate a counter's register:

    :0x0: Resets a counter and its register
    :0x1: Samples a value of a counter to its register
    :0x2: Combination of the two previous, e.g. a value of a counter is sampled
          to its register and the counter is put to reset.

----------------
UVM Verification
----------------

.. figure:: img/uvm_ver.jpg
    :align: center


Verification Plan
-----------------

TBD

Local Subcomponents
-------------------
.. toctree::
   :maxdepth: 1

   comp/input_buffer/readme
   comp/trans_buffer/readme
   comp/hdr_insertor/readme
   comp/hdr_manager/readme
   comp/software_manager/readme
