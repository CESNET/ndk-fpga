.. _tx_dma_channel_core:

Channel Core
============

.. vhdl:autoentity:: TX_DMA_CHANNEL_CORE

Behavior of the component
-------------------------
The `MFB_DROPPER` component on the input is a part of the accepting logic for
the incoming packets. A packet is accepted when channel is in the running state,
that is, enabled by its corresponding MI register. A dropping of an incoming
packet can occur when channel is stopped. In this case, a status information is
provided as a counter of discarded frames which contains the number of
discarded frames in general as well as the overall number of bytes contained
within those frames.

After the input packet is accepted, `MFB_CUTTER` is set in order to cut the PCIe
header from each incoming PCIe transaction. The payload of the transaction
is then shifted to the original SOF position, the EOF of a current transaction
is lowered by the length of a PCIe header.

When a transaction contains only usefull data, the alignment is performed in the
`ALIGN_CTL` and `MFB_DATA_ALIGNER` blocks. The alignment shifts the transactions
in sucha a way, in which they can be binded together to make a one continuous
DMA frame. This binding is then done in the `PKT_BUILD` FSM. The payload of a
frame is stored in the `MFB_DATA_FIFO` storage.

.. NOTE::
   The data FIFO needs to fit at least one frame of a length set to
   `PKT_SIZE_MAX`.

Each set of transactions, that is the frame, is delimited by the DMA header.
When DMA header is captured on the input, the data from it are deparsed to the
`MVB_HDR_FIFO` storage. After this two FIFOs indicate valid data on its outputs,
the packet is then passed to the output interface which is controlled by
`PKT_DISPATCH` FSM. A status information about the successfully sent packet is
provided via the counter of frames as well as data bytes being sent in them.

.. toctree::
   :maxdepth: 1
   :caption: Specific subcomponents

   comp/mfb_data_aligner/readme

General subcomponents
---------------------
* :ref:`mfb_dropper`
* :ref:`mfb_cutter_simple`
* :ref:`fifox`
