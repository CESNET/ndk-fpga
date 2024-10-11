.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Daniel Kondys <kondys@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. _frame_unpacker:

Frame Unpacker
--------------

.. vhdl:autoentity:: FRAME_UNPACKER

Arcitecture
~~~~~~~~~~~

The Frame Unpacker operates in the following way.
First, it extracts the length of the first individual frame of the SuperPacket from the first header (located immediately behind SOF).
To get the offset of the SOF of the following individual frame, it makes a sum of the length (from the header), length of the header (a constant), and the SOF POS (which is offset by the region it is located in).
This offset points to the *Item* behind the current frame, which means two things:

1) getting the EOF POS of the current frame means only subtracting one from the offset, and
2) getting the actual SOF POS of the next frame means rounding up the offset to the next Block.

These computations are done for all individual packets in a SuperPacket.
However, the rounded offset of the last individual frame is invalid, as it points to a Start Of Frame that does not exist.
During the unpacking process, all lengths of the individual frames are accumulated into one offset, i.e., one offset is for one whole SuperPacket.

So the whole idea behind the unpacking process consists of the following:

 - searching for the SOF and extracting the length field
 - the sum of the extracted length and the offset and its round-up and propagation

This process happens in multiple stages (generic UNPACKING_STAGES), where only a single individual packet can be "unpacked" in each stage.
That is independent of the individual frame's length and applies even when multiple individual frames are in a single word.
Therefore, the UNPACKING_STAGES value indicates the maximum amount of frames that can be unpacked from a single SuperPacket.
However, the more stages there are, the more resources the Frame Unpacker consumes.

.. _warning:
    SuperPackets containing more frames than the UNPACKING_STAGES value will result in an undefined behavior!

After the unpacking process, the headers of the individual packets are extracted and concatenated with the MVB headers from the FIFOX_MULTI.
These are then forwarded to the output on MVB or are inserted as metadata to the corresponding packets.
At the end of the pipeline, the headers of the individual packets are cut off (which does not happen during their extraction).

Block diagram
~~~~~~~~~~~~~

.. _frame_unpacker_schematic:

.. image:: img/frame_unpacker_diagram.drawio.svg
      :align: center
      :width: 100 %
      :alt:

Subcomponents
~~~~~~~~~~~~~

The Frame Unpacker has two dedicated subcomponents: the Offset Processor and the SOF Creator.
They are illustrated at the bottom of the diagram above and documented below.

**Offset Processor**

.. vhdl:autoentity:: OFFSET_PROCESSOR

**SOF Creator**

.. vhdl:autoentity:: SOF_CREATOR
