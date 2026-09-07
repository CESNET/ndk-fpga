.. _mfb_compactor:

MFB Compactor
-------------

.. vhdl:autoentity:: MFB_COMPACTOR

Component specification
________________________

The MFB_COMPACTOR removes empty (unoccupied) regions between frames on the MFB bus and
shifts the occupied regions left so that they are contiguous in the output word, while
preserving frame order and the order of regions within a frame. A region moves as one
indivisible unit, so anything short of a whole idle region is left untouched: the last
region of a frame may still be internally incomplete (``EOF_POS`` less than its maximum
value), and a region may be shared between the tail of one frame and the head of the
next - neither is a gap to be removed, only whole idle regions between frames are.

A small accumulator (up to ``REGIONS-1`` leftover regions) holds regions that did not
fill a whole output word yet; it is combined with the next input word every clock cycle,
so throughput is a full word per cycle with no extra write port needed on any downstream
memory.

Occupancy (which regions carry data of some frame, including a frame continuing through
a whole word with neither SOF nor EOF) is derived with ``MFB_AUXILIARY_SIGNALS``'s
region-level in-frame carry. That carry correctly follows a region shared between two
frames as well as a fully aligned one, so ``REGION_SIZE>1`` works for arbitrary,
non-region-aligned frame lengths too - the only real constraint is plain MFB: a single
region carries at most one SOF and one EOF.

Flow control is a global stall gating every register in the pipeline (no combinational
``SRC_RDY``/``DST_RDY`` loop). In the default First Word Fall Through mode
(``FWFT_MODE=True``) ``RX_DST_RDY = TX_DST_RDY or not TX_SRC_RDY``, so RX data keeps
falling through into the accumulator's one-word slack even while ``TX_DST_RDY='0'``, as
long as no TX word is currently waiting to be accepted. Setting ``FWFT_MODE=False``
falls back to the plain ``RX_DST_RDY <= TX_DST_RDY`` wire (one gate less on
``RX_DST_RDY``'s fan-out, at the cost of stalling RX the instant TX backpressures).

A non-empty, non-full accumulator is flushed to TX after ``FLUSH_TIMEOUT`` consecutive
clock cycles without new occupied regions arriving, so a leftover partial word does not
wait forever when the input goes idle.
