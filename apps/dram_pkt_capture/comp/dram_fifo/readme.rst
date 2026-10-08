.. _dram_fifo:

DRAM FIFO
************

.. vhdl:autoentity:: DRAM_FIFO


See :ref:`the DRAM Packet Capture application <ndk_app_dram_pkt_capture>` for
how this component is used and sized.

Structure
---------

The write side is three stages:

- ``AXIS_PACKET_LEN`` measures each incoming packet and emits its length.
- ``fifo_buffer_in`` (``AXIS_FIFO``, ``FIFO_BUFF_IN_ITEMS`` deep) holds the
  payload beats while the length is being packed.
- a shift register packs up to ``META_LEN_COUNT`` lengths into one metaword,
  which is pushed into ``meta_fifo`` (``FIFOX``, 1024 entries).

The read side is two stages: ``fifo_buffer_out`` (``FIFOX``,
``FIFO_BUFF_OUT_ITEMS`` deep) prefetches DDR words, and a two-state formatting
FSM turns them back into AXI-Stream packets.

Metaword format
---------------
The structure of a metaword depends entirely on  ``PKT_MTU``.
The following example uses ``PKT_MTU = 4096 B``

.. code-block::

    +---------+--------+---------+-----+--------+
    | PADDING | COUNT  |  P[37]  | ... |  P[0]  |
    |   12b   |   6b   |   13b   |     |  13b   |
    +---------+--------+---------+-----+--------+
     MSB                                     LSB
.. note::
    The field widths are derived, not fixed.

.. list-table::
    :header-rows: 1
    :widths: 30 42 28

    * - Constant
      - Derivation
      - Default
    * - ``LEN_WIDTH``
      - ``log2(PKT_MTU + 1)``
      - ``13``
    * - ``META_COUNT_BITS``
      - ``log2(DDR_DATA_WIDTH / LEN_WIDTH + 1)``
      - ``6``
    * - ``META_LEN_COUNT``
      - ``(DDR_DATA_WIDTH - META_COUNT_BITS) / LEN_WIDTH``
      - ``38``
    * - ``META_UNUSED_BITS``
      - remainder
      - ``12``

``COUNT`` says how many of the length slots are valid, so a partial metaword is
legal — which is what makes the flush below safe.

Write path
----------

A packet is written to DDR only when both halves are ready: ``fifo_buffer_in``
holds at least one complete packet *and* ``meta_fifo`` holds a metaword
describing it.

Each burst to memory is the metaword beat first, then that group's payload
beats. ``metaword_sent`` selects between ``meta_fifo_do`` and ``fifo_tdata`` on
``AVMM_WRITEDATA``, and the payload FIFO is popped only during payload beats.

Metaword flush
^^^^^^^^^^^^^^

A metaword is normally emitted once all 38 slots are filled. Waiting for a 38th
packet that may never arrive would strand the previous 37 in on-chip memory, so
``flush_timer`` counts cycles since the last new length and forces out a partial
word after ``FLUSH_TIMEOUT`` (``1024``) idle cycles.

Read path
---------

Prefetching is *credit-based*. ``out_fifo_credits`` starts at
``FIFO_BUFF_OUT_ITEMS``, decrements when a read is issued and increments when a
beat is popped.

A read is issued only when all three hold:

- ``diff > outstanding_read_cnt`` — there is unread data in DDR not already
  requested.
- ``out_fifo_credits > 1`` — there is somewhere to put the result.
- ``DDR_READ_EN = '1'``.

The formatting FSM has two states:

``FMT_META``
    Pops a metaword, extracts ``COUNT`` and the length array, loads the first
    length, and moves to ``FMT_PAYLOAD``.

``FMT_PAYLOAD``
    Emits payload beats. While more than one beat remains, ``TX_AXI_KEEP`` is
    all ones. On the final beat ``TX_AXI_LAST`` asserts and ``ones_mask()``
    builds a partial ``TX_AXI_KEEP`` from the bytes left. State advances only on
    an AXI handshake. When the last packet of the group completes it returns to
    ``FMT_META``.

Ring accounting and flow control
--------------------------------

``write_ptr`` and ``read_ptr`` are one bit wider than the address space. The
extra bit is a wrap flag, so ``diff = write_ptr - read_ptr`` distinguishes full
from empty:

.. code-block:: vhdl

    can_write <= '1' when diff < (FIFO_ITEMS - 1) else '0';
    can_read  <= '1' when diff > 0 else '0';
    DDR_FULL  <= not can_write;

Pointers advance on accepted AVMM transactions (``AVMM_WRITE and AVMM_READY``),
not on request assertion. Both pointers are cleared only by ``RESET``;
``DDR_READ_EN`` and ``DDR_FULL`` never move them, so data left in the ring is
read out before anything written later.

AVMM arbitration
----------------

One AVMM port serves both directions, so writes and reads are arbitrated:

.. code-block:: vhdl

    grant_write <= lock_is_write     when req_lock = '1' else write_wants;
    grant_read  <= not lock_is_write when req_lock = '1' else read_wants and not write_wants;

**Writes win.** A read is granted only when no write is pending, which maximizes RX throughput.

``req_lock`` holds a grant until the memory accepts it. Without it, a request
could switch direction mid-transaction while ``AVMM_READY`` was still low (AVMM protocol violation), and
the address would change under an in-flight request.

Sizing constraints
------------------

Two elaboration-time assertions enforce that both buffers hold at least one
full MTU packet:

.. code-block:: vhdl

    assert FIFO_BUFF_IN_ITEMS  >= PKT_MTU/(AXI_DATA_WIDTH/8)
    assert FIFO_BUFF_OUT_ITEMS >= PKT_MTU/(AXI_DATA_WIDTH/8)

.. note::
    ``FIFO_ITEMS`` must not exceed the memory actually behind the AVMM port. The
    address is truncated, so an oversized ring aliases onto itself and
    overwrites unread data. In this application the depth is derived from
    ``MEM_TARGET``; see :ref:`dram_pkt_capture_mem_interface`.

Simulation
----------

The component has its own cocotb testbench in ``cocotb/``, which drives the AXI
ports directly and answers the AVMM port with a memory model, so no card or
application core is involved.

.. code-block:: bash

    cd apps/dram_pkt_capture/comp/dram_fifo/cocotb
    make

``run_test`` sends 10000 random frames of 100–4096 B with ``DDR_READ_EN`` tied
high, and checks that what comes out of the read port matches what went in.
Generics are left at their entity defaults, so ``PKT_MTU`` is ``4096`` — exactly
the largest frame the test generates.

For the whole capture path end to end, see :ref:`dram_pkt_capture_tls`.
