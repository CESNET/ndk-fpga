.. _tx_dma_calypte:

TX DMA Calypte
==============

This is the transmitting part of the DMA Calypte core. TX direction behaves
similarly to the RX DMA Calypte. Data buffers are provided in the hardware to
which the data can be stored. The frames are output on the *USR_TX_* side and
PCI Express transactions are accepted on the *PCIE_CQ_* side. Output frame
can constist out of multiple PCIe transactions. Each such frame is delimited
by the DMA header which provides the size of the frame as well as the channel
to which the frame is designated and an address of the first byte of the
frame. PCIe transactions can be send on the unsorted series of adresses. The
DMA header then serves as delimiting block where, after its acceptance,
the frame on the output is read continuously from the address of the first
byte. The block scheme of the TX DMA Calypte controller is provided in the
following figure:

.. figure:: img/tx_calypte_block-tx_dma_calypte_top.svg
    :align: center
    :width: 1000px

.. vhdl:autoentity:: TX_DMA_CALYPTE

Control/Status Registers
------------------------

In order for the controller to be controlled by the software, an address space
with configuration/status (C/S) registers is initialized. Currently, each
channel contains its own set of registers with the overall size of 128 B. The
1st channel's registers are located on the address *0x00*, the second on *0x80*, the
third on *0x100*, etc. The address offset of the whole TX controller within the DMA
engine is *0x200000*. The registers are connected through :ref:`MI bus <mi_bus>` to
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
      - R/W
      - Reading pointer for data (up to 16 bits)
    * - 0x1C
      - Hardware header pointer (HHP)
      - R/W
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
      - -Reserved-
      - N/A
      - \-
    * - 0x44
      - -Reserved-
      - N/A
      - \-
    * - 0x48
      - -Reserved-
      - N/A
      - \-
    * - 0x4C
      - -Reserved-
      - N/A
      - \-
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
      - W/R
      - Mask for the data pointers (determines data buffer size)
    * - 0x5C
      - Header pointer mask (HPM)
      - W/R
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
    :scale: 60%


Verification Plan
-----------------

All of these tests were checked in a verification with a random seed. The verification
files are located in the ``uvm/`` directory

.. list-table:: Tab. 2
    :align: center
    :widths: 5 15 5 5 10 5
    :header-rows: 1

    * - ID
      - Description
      - Requirement level
      - Checked by
      - Status
      - Test name
    * - base
      - Simple packet transfer and check if no packets are droped/damaged on an enabled channel. Randomly
        enable/disable the channels (check the packet counters on the end).
      - Required
      - Counter check on the end of test
      - Verified
      - test::base
    * - mult_region
      - For a multiple-regions configuration vary the packet begins/ends in all regions. This puts the
        transaction buffer under stress test.
      - Required
      - Func. cover
      - Verified
      - test::base/test::speed
    * - pkt_drop
      - Check if packets are droped on a disabled channel. Check if the counters of dropped packets have
        correct values.
      - Required
      - Packet counter check on the end of a test
      - Unverified
      - test::base
    * - thrp_meas
      - Measure throughput in Gbps.
      - Optional
      - Reported periodically by the *statistics* class from the ``uvm_mfb`` environment. (The verbosity needs
        to be set to ``UVM_LOW`` in order to display these statistics)
      - Verified
      - test::speed
    * - lat_meas
      - Measure latency from input to output. Report average value, maximum,
        minimum and standard deviation. Repeat 10000 times and report values in
        the documentation.
      - Optional
      - None
      - Unverified
      - Special sequence that does measurement for a single packet.

Local Subcomponents
-------------------
.. toctree::
   :maxdepth: 1

   comp/metadata_extractor/readme
   comp/chan_start_stop_ctrl/readme
   comp/packet_dispatcher/readme
   comp/pcie_trans_buffer/readme
   comp/software_manager/readme

General Subcomponents
---------------------
* :ref:`fifox_multi`
