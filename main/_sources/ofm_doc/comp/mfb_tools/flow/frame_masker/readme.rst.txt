.. _mfb_frame_masker:

MFB Frame Masker
----------------

.. vhdl:autoentity:: MFB_FRAME_MASKER


Component specification
_______________________

The Frame Masker 2 outputs one or more frames according to the user's specification through the TX_MASK port.
This Mask (set by the user/verification) is valid with TX_DST_RDY and also with SOFs in the output word.
The TX SOF and EOF ports with the suffix "MASKED" are part of the standard output MFB interface that contains the masked frames.
However, this means that the user does not know the current available frames (SOFs) in the output word, according to which they could set the Mask.
Hence, the currently masked word (SOFs and EOFs) is available in the "UNMASKED" interface.
The "ORIGINAL" interface presents the current word that is being processed in its original form, meaning as it was on input without any Mask applied.

**The standard (MASKED) MFB output interface**

Here are the frames that the user wants to read according to the Mask.
An import thing to note is that the components takes into accord previous Masks, so it is not possible to read the same frame twice.
Once a frame is read, it will never be visible on this interface again.

**The UNMASKED interface**

This interface displays the frames that are currently available at the output.
In the output word, there are either SOFs and EOFs masked by previous Mask(s) or a brand new data word from the input (one clock period delay).
The ``TX_SRC_RDY_UNMASKED`` is set whenever masking is in process or a new valid word arrives.
When the last frame is masked, new data word is automatically loaded.
This means that there is never a word at the output where all frames have been read (= SOFs and EOFs were masked).

**The ORIGINAL interface**

Whenever a new data word arrives, it is stored in a register in the component.
It does not change values during masking, only when a new data word is loaded into it.
The ports of this interface are directly connected to the signals in this register.

Examples
________

**Example 1** demonstates a common reading of 2 packets in one clock cycle.
Note that the values of Mask can be arbitrary in Regions without SOF (SOF_UNMASKED).
So instead of Mask ``1 0 1 0``, it could be also written as ``1 x 1 x``.
The ``TX_DATA`` and MASKED signals are the standard output of the component.
The ``TX_DATA (UNMASKED)`` and ``TX_DATA (ORIGINAL)`` outputs serve just as a visual representation of the situation on the UNMASKED and ORIGINAL interfaces.

.. code-block::

    +-----------------------------------------------------------------------+
    |                                                                       |
    |    REGION:                   0         1         2         3          |
    |                                                                       |
    |                                                                       |
    |    RX_SOF:                   1         0         1         0          |
    |                         +---------+---------+---------+---------+     |
    |    RX_DATA:             |     @@@@|@@@@     |  @@@@@  |         |     |
    |                         +---------+---------+---------+---------+     |
    |    RX_EOF:                   0         1         1         0          |
    |                                                                       |
    |                                                                       |
    |    TX_MASK:                  1         0         1         0          |
    |                                                                       |
    |                         +---------+---------+---------+---------+     |
    |    TX_DATA:             |     @@@@|@@@@     |  @@@@@  |         |     |
    |                         +---------+---------+---------+---------+     |
    |    TX_SOF_MASKED:            1         0         1         0          |
    |    TX_EOF_MASKED:            0         1         1         0          |
    |                                                                       |
    |                         +---------+---------+---------+---------+     |
    |    TX_DATA (UNMASKED):  |     @@@@|@@@@     |  @@@@@  |         |     |
    |                         +---------+---------+---------+---------+     |
    |    TX_SOF_UNMASKED:          1         0         1         0          |
    |    TX_EOF_UNMASKED:          0         1         1         0          |
    |                                                                       |
    |                         +---------+---------+---------+---------+     |
    |    TX_DATA (ORIGINAL):  |     @@@@|@@@@     |  @@@@@  |         |     |
    |                         +---------+---------+---------+---------+     |
    |    TX_SOF_ORIGINAL:          1         0         1         0          |
    |    TX_EOF_ORIGINAL:          0         1         1         0          |
    |                                                                       |
    +-----------------------------------------------------------------------+

**Example 2** demonstrates reading 2 packets one-by-one, each in one clock cycle.
Notice how in the second clock cycle (on the right), the SOF_ORIGINAL stays the same.
It will stay the same until a new data word is loaded.
Menawhile, the SOF_UNMASKED is without the SOF in Region 0, as that packet has already been read.
These "rules" also apply for the respective EOF signals.

.. code-block::

    +-----------------------------------------------------------------------------------------------------------------+
    |                                                                                                                 |
    |    TIME:                --------->                                                                              |
    |                                                                                                                 |
    |    REGION:                   0         1         2         3            0         1         2         3         |
    |                                                                                                                 |
    |                                                                                                                 |
    |    RX_SOF:                   1         0         1         0                                                    |
    |                         +---------+---------+---------+---------+                                               |
    |    RX_DATA:             |     @@@@|@@@@     |  @@@@@  |         |                                               |
    |                         +---------+---------+---------+---------+                                               |
    |    RX_EOF:                   0         1         1         0                                                    |
    |                                                                                                                 |
    |                                                                                                                 |
    |    TX_MASK:                  1         0         0         0            0         0         1         0         |
    |                                                                                                                 |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA:             |      @@@@|@@@@    |         |         |  |         |         |  @@@@@  |         |    |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_MASKED:            1         0         0         0            0         0         1         0         |
    |    TX_EOF_MASKED:            0         1         0         0            0         0         1         0         |
    |                                                                                                                 |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA (UNMASKED):  |      @@@@|@@@@    |  @@@@@  |         |  |         |         |  @@@@@  |         |    |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_UNMASKED:          1         0         1         0            0         0         1         0         |
    |    TX_EOF_UNMASKED:          0         1         1         0            0         0         1         0         |
    |                                                                                                                 |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA (ORIGINAL):  |      @@@@|@@@@    |  @@@@@  |         |  |      @@@@|@@@@    |  @@@@@  |         |    |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_ORIGINAL:          1         0         1         0            1         0         1         0         |
    |    TX_EOF_ORIGINAL:          0         1         1         0            0         1         1         0         |
    |                                                                                                                 |
    +-----------------------------------------------------------------------------------------------------------------+

**Example 3** shows that the packets are automatically read across multiple words (when the Mask is set so).
Here, the second packet from the example 2 is extended to end in the following data word.
The Mask is set to read the packet, so its first part is at the output immediately and the rest of it is sent in the following data word without any delays.

.. code-block::

    +-----------------------------------------------------------------------------------------------------------------+
    |                                                                                                                 |
    |    TIME:                --------->                                                                              |
    |                                                                                                                 |
    |    REGION:                   0         1         2         3            0         1         2         3         |
    |                                                                                                                 |
    |                                                                                                                 |
    |    RX_SOF:                   0         0         1         0            0         0         1         0         |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    RX_DATA:             |         |         |   @@@@@@|@@@@@@@@@|  |@@@@@@@@@|@@@      |   @@@@@@|@@@@     |    |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    RX_EOF:                   0         0         0         0            0         1         0         1         |
    |                                                                                                                 |
    |                                                                                                                 |
    |    TX_MASK:                  0         0         1         0            0         0         0         0         |
    |                                                                                                                 |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA:             |         |         |   @@@@@@|@@@@@@@@@|  |@@@@@@@@@|@@@      |         |         |    |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_MASKED:            0         0         1         0            0         0         0         0         |
    |    TX_EOF_MASKED:            0         0         0         0            0         1         0         0         |
    |                                                                                                                 |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA (UNMASKED):  |         |         |   @@@@@@|@@@@@@@@@|  |@@@@@@@@@|@@@      |   @@@@@@|@@@@     |    |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_UNMASKED:          0         0         1         0            0         0         1         0         |
    |    TX_EOF_UNMASKED:          0         0         0         0            0         1         0         1         |
    |                                                                                                                 |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA (ORIGINAL):  |         |         |   @@@@@@|@@@@@@@@@|  |@@@@@@@@@|@@@      |   @@@@@@|@@@@     |    |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_ORIGINAL:          0         0         1         0            0         0         1         0         |
    |    TX_EOF_ORIGINAL:          0         0         0         0            0         1         0         1         |
    |                                                                                                                 |
    +-----------------------------------------------------------------------------------------------------------------+

.. note::
    In certain cases, the component allows the user to skip (=discard) some frames.
    This may or may not be an unwanted behaviour.
    It does not occur for a 1-Region configurations.
    The cases, when a frame is skipped, are as follows:

        - there are multiple SOFs in the output word (the UNMASKED interface) and
        - the Mask is ``0`` for one or more SOFs in the lower Regions and ``1`` in a higher Region.

    Such situation is displayed in the following example.

**Example 4** shows how to skip (discard) a frame.
After setting the Mask to ``0 0 1 0``, only the second frame is read from the output.
And because this is the last frame in the current data word, the next one is loaded.
It is visible on the UNMASKED and ORIGINAL intefaces, but the user set the mask to ``0 0 0 0``, so it is not read.
However, this one will wait there until it is read, because it is the last (and only) packet in the data word.
This packet cannot be skipped.

.. code-block::

    +-----------------------------------------------------------------------------------------------------------------+
    |                                                                                                                 |
    |    TIME:                --------->                                                                              |
    |                                                                                                                 |
    |    REGION:                   0         1         2         3            0         1         2         3         |
    |                                                                                                                 |
    |                                                                                                                 |
    |    RX_SOF:                   1         0         1         0            1         0         0         0         |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    RX_DATA:             |     @@@@|@@@@     |  @@@@@  |         |  |   @@@@@@|@@@@@@@@@|@@@@@@@@@|@@       |    |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    RX_EOF:                   0         1         1         0            0         0         0         1         |
    |                                                                                                                 |
    |                                                                                                                 |
    |    TX_MASK:                  0         0         1         0            0         0         0         0         |
    |                                                                                                                 |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA:             |          |        |  @@@@@  |         |  |         |         |         |         |    |
    |                         +----------+--------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_MASKED:            0         0         1         0            0         0         0         0         |
    |    TX_EOF_MASKED:            0         0         1         0            0         0         0         0         |
    |                                                                                                                 |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA (UNMASKED):  |     @@@@|@@@@     |  @@@@@  |         |  |   @@@@@@|@@@@@@@@@|@@@@@@@@@|@@       |    |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_UNMASKED:          1         0         1         0            1         0         0         0         |
    |    TX_EOF_UNMASKED:          0         1         1         0            0         0         0         1         |
    |                                                                                                                 |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_DATA (ORIGINAL):  |     @@@@|@@@@     |  @@@@@  |         |  |   @@@@@@|@@@@@@@@@|@@@@@@@@@|@@       |    |
    |                         +---------+---------+---------+---------+  +---------+---------+---------+---------+    |
    |    TX_SOF_ORIGINAL:          1         0         1         0            1         0         0         0         |
    |    TX_EOF_ORIGINAL:          0         1         1         0            0         0         0         1         |
    |                                                                                                                 |
    +-----------------------------------------------------------------------------------------------------------------+

.. note::
    The examples are simplified and do not take into account the latency of the component.
    With the generic ``USE_PIPE = False``, the OUTPUT DATA would be delayed one clock period.
    If it is set to ``True``, the delay would be two clock periods.

Verification plan
_________________

.. list-table:: Tab. 1
    :align: center
    :widths: 5 15 5 5 10 5
    :header-rows: 1

    * - ID
      - Description
      - Requirement level
      - Checked by
      - Status
      - Test name
    * - 1
      - Skip (=discard) some packets.
      - Obligatory
      - Func. cover
      - Verified
      - test::ex_test
    * - 2
      - Read all packets without skipping any of them. This is the most realistic use-case of the component.
      - Obligatory.
      - Func. cover
      - Unverified, the speed test needs adjustments to set the Mask to avoid skipping packets.
      - test::speed
    * - 3
      - Read all packets (no skips) and no more than one in each clock cycle.
      - Optional
      - Func. cover
      - Unverified
      - N/A
    * - 4
      - Verify that the UNMASKED interface behaves correctly. This interface is expected to be used intensly.
      - Obligatory
      - Func. cover (?)
      - Partially Verified - the SOF_UNMASKED is tapped by a probe and used in the Model to skip packets.
      - test::ex_test
    * - 5
      - Verify that the ORIGINAL interface behaves correctly.
      - Optional
      - Func. cover (?)
      - Unverified
      - N/A
