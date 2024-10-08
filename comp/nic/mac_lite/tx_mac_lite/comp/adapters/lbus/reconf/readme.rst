.. _mfb_to_lbus_reconf:

MFB -> LBUS reconfigurator (TX LBUS)
====================================
This component converts frames from the input with MFB#(1,8,8,8) configuration to the output
with MFB#(1,4,16,8) configuration. The behavior of the output transmission
abides also by the `LBUS specification
<https://docs.xilinx.com/r/en-US/pg165-cmac/User-Side-LBUS-Interface>`_. This
component has been made solely for this purpose. Its mode of operation is
similar to the :ref:`mfb_reconfigurator` component (with corresponding generic
parameters). A specific design of this kind allows to better meet the timing
requirements.

.. vhdl:autoentity:: MFB_TO_LBUS_RECONF
   :noautogenerics:

Operation
---------
The input frame transactions meet the MFB specification while the outgoing
meet the LBUS specification. The second one is similar to the
first with following differences:

1. Outgoing frames have to be transmitted without interruption from
   `TX_SOF` to `TX_EOF` (the `TX_SRC_RDY` must not be deasserted
   inside a frame). The frames at the input already respect this rule.
2. When two frames occur in a single word, the second frame has to start
   in the block right after the one where the previous frame has ended.
3. When there is only one frame beginning in the word, its beginning has to be
   aligned to the beginning of the word.
4. The only case in which a gap inside a frame can occur, is when the receiving
   side uses the backpressure functionality by deasserting the `TX_DST_RDY`
   signal

Another rule applies to the supported frame lengths. The component has been
designed to process frames as small as 60B and increasing to arbitrary large
ones.


Controlling state machine
-------------------------
The internal design consists of two `BARREL_SHIFTER_GEN` components which are
controlled by the `sh_fsm` state machine. The simplified transition diagram
looks like the following:

.. figure:: doc/adapter_fsm-Simplified.svg
   :width: 50%
   :align: center

Next follows a short description of the behavior in each state.

IDLE
^^^^
The state machine is reset into the `IDLE` state. The FSM waits for a
frame to come and sets the proper shift on the output according to the frames
`RX_SOF_POS` value. Two consecutive words are buffered on the input every time and
the shift on the output is performed over both of them. This is because a single
word would not be always sufficient to fully fill the output word after the
shift. This state also handles the situation in which a single frame begins and
also ends in one input word or can be shifted in such a way in which this
situation occurs.

PKT_PROCESS
^^^^^^^^^^^^
The `PKT_PROCESS` state processes the frame after receiving a `SOF`.
The shifting does not change in this state. Sometimes, when there is an
`EOF` in the first register, the shifting can be set to a
value where the `EOF` appears in the output word (see
:ref:`mfb_to_lbus_reconf_scenario5`). In that case, the output is sent out and
the content of the register with `EOF` is ignored in the next cycle.

PKT_END
^^^^^^^^
The `PKT_END` state is entered when there is an `RX_EOF` of a currently
processed frame. The output MFB signals are set and the `TX_EOF_POS` is set
according to the value by which the frame has been shifted.

WORD_REALIGN
^^^^^^^^^^^^^
The `WORD_REALIGN` state takes care of the situation when two frames occur in a
single word (one frame ends and another begins). The shift of the
ending frame remains unchanged. On the output, the beginning frame is shifted to
the block immediately after the block in which a previous frame has ended.

.. _mfb_to_lbus_reconf_sh_dir:

The majority of the shifting is performed in the *DOWN* direction, that is from MSB
to LSB, from a block with a higher index to a block with a lower index. However,
there is a situation in which a shift needs to be done in the opposite direction (see the
left half of the picture in :ref:`mfb_to_lbus_reconf_scenario4`), e.g. the
`RX_SOF` of the beginning frame has to be shifted to the block with a higher
index(*UP* direction or shifting from LSB to MSB). For example, when `RX_EOF` of
the preceding frame and the `RX_SOF` of the following occur on input blocks
indexed 2 and 3 respectively (blocks are indexed from 0). Adding to that, the
ending frame is not shifted and remains in place. Because the output has half
the number of blocks as the input and with respect to the MFB specification,
the beginning frame needs to be shifted to a block with a higher index on the
output. In this case, the input buffer needs to be stopped because of an
unprocessed block in the first word of the input buffer and that is when the
`PKT_HALT` state comes into place.

PKT_HALT
^^^^^^^^
The input buffer is stopped because the last block remains in the first word.
The shift is set to the usual *DOWN* direction (to the 0th block) and the
processing of the frame continues (see the right half of the picture in
:ref:`mfb_to_lbus_reconf_scenario4`).


Examples of realignment
-----------------------
The following figures show various forms of realignment of an input frame. The
resolution of those examples is done with respect to MFB blocks. The input
configuration is MFB #(1,8,8,8) and the output is MFB #(1,4,16,8). This is shown
in the following figure:

.. figure:: doc/mfb_lbus_reconf_realignment-General.svg
   :width: 20%
   :align: center

.. note::
   Notice that the input and output words are of the same length.

Scenario 1
^^^^^^^^^^

.. figure:: doc/mfb_lbus_reconf_realignment-Simple_real.svg
   :width: 20%
   :align: center

This figure shows the simplest case in which a basic shift is performed. The
`RX_SOF` is read in the first register and the frame is shifted
accordingly. The output word consists of two parts of the *A* frame,
the *A2* is taken from the second register of the input buffer and the *A1* part
is taken from the first register of the buffer.

.. note::
   The buffering goes from the `RX_MFB\_\*` input of the component to the first register
   and then to the second register.

Scenario 2
^^^^^^^^^^

.. figure:: doc/mfb_lbus_reconf_realignment-Shift_whole.svg
   :width: 20%
   :align: center

A small frame named *A* begins in the second register and ends in the first,
but after the shift, the frame moves entirely to the output word. There is no
need to care for the B frame because it can be processed in the following cycle.

Scenario 3
^^^^^^^^^^

.. figure:: doc/mfb_lbus_reconf_realignment-Two_together.svg
   :width: 20%
   :align: center

Two frames occur in the second register, the realignment of the word is done
by only shifting the *B* frame. The frame *B*
consists of the content of both of the input registers.

.. note::
   The frame *A* on the input is shown here without the shift for simplicity.
   In real-world conditions, the *A* frame often has its own shifting based on
   its `SOF_POS` value gained in previous transactions.

.. _mfb_to_lbus_reconf_scenario4:

Scenario 4
^^^^^^^^^^

.. figure:: doc/mfb_lbus_reconf_realignment-Two_together_back.svg
   :width: 50%
   :align: center

The ending frame *A* is not shifted and the *B* frame is shifted in the *UP*
direction. The reversal of the
usual shifting direction is done in order to adhere to the rules of the MFB
specification where the beginning of a frame needs to be aligned to a block. So
the `SOF` of the *B* frame is shifted to the next block following the `EOF` of
the previous frame.

The input buffer is stopped in this cycle because there is an unprocessed block
of the *B* in the second register. In the second cycle (right half of the
picture) the shifting returns to the usual direction and the remaining block
with another content of the *B* frame from the first register is shifted to the
beginning of the word on the output.

.. _mfb_to_lbus_reconf_scenario5:

Scenario 5
^^^^^^^^^^

.. figure:: doc/mfb_lbus_reconf_realignment-End_to_curr.svg
   :width: 20%
   :align: center

The frame *A* undergoes ordinary shifting where the shadowed part has been
processed previously. The current shift causes the `EOF` of a current frame to
appear in the output word so the content of the first register is already
processed in the current cycle. The component then waits for the arrival of the
next frame.

Scenario 6
^^^^^^^^^^

.. figure:: doc/mfb_lbus_reconf_realignment-End_to_curr_sec.svg
   :width: 20%
   :align: center

This case is a slight modification of the previous one. The current shift causes
the *A* frame to appear entirely in the output word. In the next cycle, only the
`SOF` of the *B* frame is processed because the `EOF` of the *A* has already
been sent out.
