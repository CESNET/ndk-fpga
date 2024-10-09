.. _mfb_pd_asfifo:

MFB Packet Discard ASFIFO
-------------------------

The Packet Discard ASFIFO is an asynchronous FIFO with the ability to erase (discard) MFB frames (packets).
For each packet put inside, the user specifies if the packet is to be discarded (information valid with EOF).
If so, the packet will not appear on the ASFIFO output.
Because the information about discarding is only available with the EOF, the unit works in store-and-forward mode (each packet has to be stored completely before we can decide whether to propagate it further).

Architecture
^^^^^^^^^^^^

.. _mfb_pd_asfifo_basic:

.. image:: doc/pd_asfifo.svg
      :align: center
      :width: 100 %
      :alt:

The internal architecture of the unit consists of multipe stages.

If a packet has both SOF and EOF in the same data word (single-word packet), it can be discarded immidiately by masking of the SOF and EOF to 0.

If the packet continues to the next word (there can only by 1 such packet in each data word), the unit starts storing its data into the Mark ASFIFO.
At the same time, it "marks" the address possition of the SOF data word in the ASFIFO BRAM (WR PTR Marked).
Once the data word with the EOF arrives (together with the information to discard / propagate the packet further), one of two things will happen:

#. If the packet is meant to be discarded, the WR PTR in the Mark ASFIFO resets back to the position of the WR PTR Marked (freeing the space in the buffer taken by the discarded packet).
#. Otherwise the WR PTR stays the same and the WR PTR Marked is propagated to the read side, which enables propagation of the packet's data to output.

Since the data word where the packet started might contain valid data of another packet, it cannot be deleted and overwritten by the WR PTR shift.
This data word is propagated to the output, but the last SOF in it must be masked.
To be able to do this, the information about the multi-word packet discarding is propagated through the Masking ASFIFO.
From this ASFIFO, the Mark ASFIFO reading logic knows, whether the SOF should be removed or not.

Additional Features
^^^^^^^^^^^^^^^^^^^

Force Discard
=============

The Force Discard feature can be used to immidiately start discarding packets.
When Force Discard is active, the currently processed packet is discarded as well as all following packets as long as the signal is active.
Once the signal falls to 0, the next valid word **must start with a SOF**.
If there is an EOF in the word before the SOF at this point, the user must set it to 0 himself.

The feature is useful when the PD ASFIFO fills up, but the user logic before it has no DST_RDY to stop the incoming data.
This way the user can continue sending new words to the full ASFIFO while having them all discarded.
