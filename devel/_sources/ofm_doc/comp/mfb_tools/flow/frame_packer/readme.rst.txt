.. readme.rst: Documentation of single component
.. Copyright (C) 2024 CESNET z. s. p. o.
.. Author(s): David Beneš <xbenes52@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. _frame_packer:

Frame Packer
------------

.. _frame_packer_schematic:

.. image:: img/frame_packer.svg
      :align: center
      :width: 100 %
      :alt:

.. vhdl:autoentity:: FRAME_PACKER

Architecture
~~~~~~~~~~~~

The Frame Packer operates in the following way.
The MFB and MVB has to be synchronized as the channel ID of each packet is used to sort incoming packets.
This is done at the input using a :ref:`Metadata Insertor<metadata_insertor>`.


The following component in the pipeline named as ``Auxiliary generator`` is used to extract the auxiliary data used to calculate the select signal for each :ref:`Barrel Shifter<barrel_shifter>` and to recreate the MFB protocol in each channel unit (packet accumulator).
The protocol recreation is necessary as shifting the input data will invalidate MFB protocol.
The auxiliary data is generated separately for each packet in the MFB word, resulting in multiple vectors: ``slv_array_t(MFB_REGIONS downto 0)(...)``.
Additionaly is each packet filtred to its own vector ``slv_array_t(MFB_REGIONS downto 0)(...)``.
The following list summarizes the data generated:

1. TX_CHANNEL_BS - Channel ID of each packet
2. TX_PKT_LNG - Length of the current packet (valid with SOF)
3. TX_BLOCK_VLD - Valid blocks in binary format (one valid bit per each valid block)
4. TX_SOF_ONE_HOT - SOF_POS in one hot format
5. TX_EOF_ONE_HOT - EOF_POS in one hot format
6. TX_SOF_POS_BS - SOF_POS for calculation of select signal

For the calculation of the select signal for each packet a component named ``BS_CALC`` is used.
The parameters of the calculation are the status ``pointer``, the number of ``valid blocks`` and the ``SOF_POS`` of the packet within the MFB.
When the shift select is being calculated, the packets are routed to the Barrel Shifters (one per packet).
Its purpose is to rotate the MFB word so that the data can be easily assembled in each channel unit.
The first Barrel Shifter is used for packets that originates in the previous words.
Other Barrel Shifters are used for packets that begins in the current word. 
The packet starting in the first region is processed by the barrel shifter with index ``1``, the packet starting in the second region is processed by the barrel shifter with index ``2``, and so on.
Along with the packets, the previously generated auxiliary signals are shifted as well.

After the MFB word is shifted, the packets and their auxiliary signals are redistributed to the channels according to their channel ID.
Each channel unit begins with MUX array that selects data based on the valid blocks array that arrives along with shifted data.
Each MUX passes the block according to its index.
The input of the MUXs comes from the Barrel Shifters (the number of MUX inputs depends on the number of Barrel Shifters).

.. _packet_accumulator_schematic:

.. image:: img/packet_accumulator.svg
      :align: center
      :width: 100 %
      :alt:

After the data is selected, it is either stored in a temporary register or sent for further processing.
This temporary register (assembly register) is used to store data until the whole word is full of valid data.
Its status is monitored by the status ``pointer``, which is also used for the calculation of shift select signal.

When the assembly register is full, its contents, along with auxiliary signals, are passed to the next stage and the MFB protocol is re-created.
Assembled word is sent to the FIFO and its length is sent to the ``SPKT_LNG`` unit that controls the length of the Super-Packet.
The Super-Packet length is calculated from the length of regular packets that are stored in the FIFO.

Once the desired length is reached or the timeout is triggered, the content of the FIFO is sent to the output.
The MFB protocol of the Super-Packet is created in the ``FIFO_CTRL`` unit, which masks the SOF and EOF of partial packets.

At the output of the ``FRAME_PACKER`` is a simplified version of the ``MFB_MERGER``, which passes the Super-Packets from each channel to the output.
Along with the Super-Packets, its length and its channel ID are read from the channel as well.
The length and the channel ID are sent to the ``MVB_FIFO`` which is directly connected to the output MVB interface.

References
~~~~~~~~~~
For more detailed description refer to `David Beneš's master thesis <https://www.vut.cz/www_base/zav_prace_soubor_verejne.php?file_id=267988>`_  (2023/2024)
 